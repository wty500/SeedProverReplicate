# main.py
import asyncio
import json
import os
import subprocess
import re
from typing import List, Tuple, Optional, Dict, Set
from dataclasses import dataclass, field
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
from pathlib import Path
import openai
import logging
from openai import AsyncOpenAI  # 新增：异步客户端

logger = logging.getLogger("SeedProverRep")


def setup_logging(log_file: str = "seedprover.log", level: int = logging.INFO) -> None:
    """Configure logging to output to console and file."""
    logger.setLevel(level)
    if logger.handlers:
        return  # Already configured

    fmt = logging.Formatter(
        fmt="%(asctime)s | %(levelname)s | %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )

    # Console handler
    ch = logging.StreamHandler()
    ch.setLevel(level)
    ch.setFormatter(fmt)
    logger.addHandler(ch)

    # File handler
    fh = logging.FileHandler(log_file, encoding="utf-8")
    fh.setLevel(level)
    fh.setFormatter(fmt)
    logger.addHandler(fh)


@dataclass
class Lemma:
    name: str
    statement: str
    description: str = ""
    proof: Optional[str] = None
    difficulty: float = 1.0
    dependencies: List[str] = field(default_factory=list)
    proof_attempts: int = 0

class LeanCompiler:
    """处理Lean代码编译和反馈"""

    def __init__(self, project_dir="project"):
        self.project_dir = project_dir

    def write_lean_file(self, filename: str, content: str):
        """写入Lean文件"""
        filepath = os.path.join(self.project_dir, filename)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)

    def compile(self, lean_code:str, timeout=3000) -> Tuple[bool, str]:
        """编译项目并返回结果"""
        self. write_lean_file("main.lean", lean_code)
        try:
            result = subprocess.run(
                ["lake", "build"],
                cwd=self.project_dir,
                capture_output=True,
                text=True,
                timeout=timeout,
                encoding='utf-8'
            )

            if result.returncode == 0:
                return True, "Compilation successful"
            else:
                error_msg = result.stdout
                return False, self._parse_error(error_msg, lean_code)
        except subprocess.TimeoutExpired:
            return False, "Compilation timeout"
        except Exception as e:
            return False, str(e)

    def _parse_error(self, error_msg: str, lean_code: str) -> str:
        """解析Lean错误信息"""
        # 提取最相关的错误信息
        lines = error_msg.split('\n')
        relevant_lines = []
        for line in lines:
            if 'set_option linter.docPrime false' in line.lower():
                raise RuntimeError(line)
            if 'trace:' in line.lower() or 'warning:' in line.lower() or 'info:' in line.lower() or 'set_option diagnostics true' in line.lower() or 'note:' in line.lower():
                continue
            relevant_lines.append(line)
            match = re.search(r'main\.lean:(\d+):', line)
            if match:
                line_num = int(match.group(1))
                code_lines = lean_code.split('\n')
                if 0 < line_num <= len(code_lines):
                    error_line = code_lines[line_num - 1]
                    relevant_lines.append(f"    > On line {line_num}: {error_line.strip()}")
        return '\n'.join(relevant_lines) if relevant_lines else error_msg

class SeedProver:
    """SeedProver主类"""

    def __init__(self, api_key: str, model="gemini-2.5-pro-thinking"):
        self.client = AsyncOpenAI(api_key=api_key, base_url="http://xxxxx/v1/")  # 改为异步客户端
        self.model = model
        self.compiler = LeanCompiler()
        self.lemma_pool: List[Lemma] = []
        self.proved_lemmas: Set[str] = set()
        self.compile_lock = asyncio.Lock()

    async def prove(self, statement: str, strategy="medium") -> Optional[str]:
        """主证明入口"""
        logger.info(f"Starting proof with {strategy} strategy for: {statement[:100]}...")

        if strategy == "light":
            return await self.light_inference(statement)
        elif strategy == "medium":
            return await self.medium_inference(statement)
        elif strategy == "heavy":
            return await self.heavy_inference(statement)
        else:
            raise ValueError(f"Unknown strategy: {strategy}")

    async def light_inference(self, statement: str, max_rounds=2, max_iterations=8) -> Optional[str]:
        """Light推理策略：迭代优化证明"""
        logger.info(f"[Attempting] Statement: {statement}")

        # 初始化聊天记录
        history = []

        for round_num in range(max_rounds):
            logger.info(f"--- Round {round_num + 1} ---")

            # 初始证明生成
            proof, history = await self._generate_proof(statement, history=history)

            for iteration in range(max_iterations+1):
                logger.info(f"--- Iteration {iteration + 1} ---")
                success, refined_proof, history = await self._refine_proof(statement, proof, history, skip=(iteration==max_iterations))
                if success:
                    logger.info(f"Proof found in round {round_num+1}, iteration {iteration+1}")
                    return refined_proof
                proof = refined_proof
        return None

    async def medium_inference(self, statement: str, initial_lemmas: Optional[List[Lemma]] = None) -> Optional[str]:
        """
        Medium 推理流程：
        1) 先让 LLM 生成整份“whole proof”（若干 lemma + 主定理 main_theorem）。
        2) 编译失败 → 从这份代码里抽取 fail lemma（按出现的 lemma 解析）。
        3) 对这些 fail lemma 分别跑 light inference（8×8）得到可用证明，纳入“新上下文”。
        4) 将“已证引理”作为上下文，重新生成 whole proof。
        5) 循环往复，直到编译通过或达上限。
        """
        import re
        from typing import Dict

        # 已证明的引理池（使用传入的引理进行初始化）
        proved_bank: Dict[str, Lemma] = {lm.name: lm for lm in initial_lemmas if lm.proof} if initial_lemmas else {}
        if initial_lemmas:
            logger.info(f"[Medium] Initialized with {len(proved_bank)} externally proved lemmas.")

        # 外层/内层配置
        outer_rounds = 5
        inner_parallel = 80

        # 为“whole proof”生成保留一点对话上下文（仅用于该函数内）
        history: List[Dict[str, str]] = []

        # 与 _create_lean_file 保持一致的头部
        header = """import Mathlib
import Aesop
import Mathlib.Tactic.Ring
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial
    """

        # 简单稳健地抽取 lemma（兼容参数括号与类型冒号；只取“:= by”之前的声明部分，且将冒号包含在声明里）
        # 解释：
        # - 组1捕获引理名
        # - 组2捕获“(参数)/{隐式参数}/[实例]… : 结论”这一整段（包含冒号），避免把参数里的冒号误当成类型冒号
        lemma_pat = re.compile(
            r"(?ms)^\s*lemma\s+([A-Za-z_][A-Za-z0-9_']*)\s*((?:[\(\{\[].*?[\)\}\]]\s*)*:\s*.*?)\s*:=\s*by\b"
        )

        for outer in range(1, outer_rounds + 1):
            logger.info(f"[Medium] Outer round {outer} — generate whole proof with {len(proved_bank)} proved lemmas as context")

            # 将“已证引理”编码为可直接放入 Lean 文件顶层的代码段
            context_code = ""
            if proved_bank:
                blocks = []
                for lm in proved_bank.values():
                    if not lm.proof:
                        continue
                    # 注意：这里用于实际 Lean 代码，采用标准 Lean 4 语法（带冒号）
                    blocks.append(f"lemma {lm.name} {lm.statement} {lm.proof}")
                context_code = "\n\n".join(blocks)

            proved_lemmas = "\n\t\t".join(f"{lm.name} {lm.statement}" for lm in proved_bank.values()) if proved_bank else "(none)"
            prompt = f"""You are a Lean 4.14 prover. Produce ONE code block with this structure:

    1) A set of helpful lemmas or intermediate results that would assist in proving the main theorem. Each lemma must be syntactically correct and provable in Lean 4.14 with Mathlib imported. Use valid Lean syntax and avoid Lean 3 notations like `∀`. Do NOT use `sorry` or `admit`. Each lemma should be in the form:
    `lemma name <variable> : <statement> := by ...`
    e.g. `lemma my_lemma (x : ℝ) : x + 0 = x := by ring`
    2) Then finish with the main theorem, named EXACTLY:
    `theorem main_theorem {statement} := by ...`

    Rules:
    - Do NOT include any imports/options; only lemmas and the theorem.
    - Avoid `sorry`/`admit`.
    - Existing lemmas:
        {proved_lemmas}
    Do NOT reuse these names.
    - You MAY use those existing lemmas as if they are already defined earlier in the file.
    """
            msgs = history + [{"role": "user", "content": prompt}]
            whole_code, full_msg = await self._call_llm(msgs, temperature=0.5)
            history = msgs + [{"role": "assistant", "content": full_msg}]

            # 组合为可编译的 Lean 文件（把“已证引理”放在生成内容之前）
            compiled_code = header + (context_code + "\n\n" if context_code else "") + whole_code.strip() + "\n"

            # === 2) 编译 whole proof ===
            ok, fb = await asyncio.to_thread(self.compiler.compile, compiled_code)
            if ok:
                logger.info("[Medium] Whole proof compiled successfully.")
                # 将（上下文引理 + LLM 产生的新引理）与主定理体拼接为返回格式：
                #   preface(仅引理) + '\n' + (':= by ...')
                # 先从 LLM 产物中切出 main_theorem 的 body
                m_body = re.search(r"(?ms)^\s*theorem\s+main_theorem\b.*?(?P<body>:=\s*by[\s\S]*)$", whole_code)
                if not m_body:
                    # 若 LLM 没按约定命名，兜底为仅用“已证引理”来完成主定理
                    main_body = await self._prove_with_lemmas(statement, list(proved_bank.values()))
                    if main_body:
                        return (context_code + "\n\n" + main_body) if context_code else main_body
                    return None

                # 取 LLM 代码里、theorem main_theorem 之前的部分，剔除掉 theorem 头本身（只保留新引理）
                idx_theorem = re.search(r"(?m)^\s*theorem\s+main_theorem\b", whole_code)
                preface_llm = whole_code[:idx_theorem.start()] if idx_theorem else ""
                # 返回值应是：已有上下文引理 + 新生成的引理 + 主定理体（:= by ...）
                preface_all = "\n\n".join(s for s in [context_code, preface_llm.strip()] if s.strip())
                body = m_body.group("body").strip()
                return (preface_all + "\n\n" + body).strip() if preface_all else body

            # 如果编译失败，进入重试循环
            for attempt in range(8): # 最多重试8次
                logger.info(f"[Medium] Whole proof failed. Retrying with feedback (Attempt {attempt + 1}/8)...")
                logger.error("[Error Message]:\n" + "="*25 + f"\n{fb}\n" + "="*25)

                # 请求LLM修复证明
                refine_prompt = f"""The previous Lean 4 proof failed with an error. Please fix it and return ONE Lean 4.14 code block containing the complete proof (lemmas and the main theorem).
Error message:
{fb}
"""
                refine_msgs = history + [{"role": "user", "content": refine_prompt}]
                whole_code, full_msg = await self._call_llm(refine_msgs, temperature=0.5)
                history = refine_msgs + [{"role": "assistant", "content": full_msg}]

                # 重新组合并编译
                compiled_code = header + (context_code + "\n\n" if context_code else "") + whole_code.strip() + "\n"
                ok, fb = await asyncio.to_thread(self.compiler.compile, compiled_code)

                if ok:
                    logger.info("[Medium] Whole proof compiled successfully after refinement.")
                    # 成功后的逻辑与上面相同
                    m_body = re.search(r"(?ms)^\s*theorem\s+main_theorem\b.*?(?P<body>:=\s*by[\s\S]*)$", whole_code)
                    if not m_body:
                        main_body = await self._prove_with_lemmas(statement, list(proved_bank.values()))
                        if main_body:
                            return (context_code + "\n\n" + main_body) if context_code else main_body
                        return None
                    idx_theorem = re.search(r"(?m)^\s*theorem\s+main_theorem\b", whole_code)
                    preface_llm = whole_code[:idx_theorem.start()] if idx_theorem else ""
                    preface_all = "\n\n".join(s for s in [context_code, preface_llm.strip()] if s.strip())
                    body = m_body.group("body").strip()
                    return (preface_all + "\n\n" + body).strip() if preface_all else body

            logger.info("[Medium] Whole proof still failed after 8 retries; extracting candidate fail lemmas...")
            # === 3) 提取这次 whole proof 中出现的 lemma，选未证明的做 inner light inference ===
            candidates: List[Lemma] = []
            seen: Set[str] = set()
            for m in lemma_pat.finditer(whole_code):
                name = m.group(1).strip()
                stmt = m.group(2).strip()
                if name and stmt and (name not in proved_bank) and (name not in seen):
                    candidates.append(Lemma(name=name, statement=stmt))
                    seen.add(name)

            if not candidates:
                logger.info("[Medium] No new lemmas found from this whole proof; continuing to next outer round.")
                continue

            sem = asyncio.Semaphore(inner_parallel)

            async def prove_one(lm: Lemma) -> Optional[Lemma]:
                async with sem:
                    prf = await self.light_inference(lm.statement, max_rounds=1, max_iterations=8)
                    if prf:
                        lm.proof = prf  # prf 形如 " := by ..."
                        return lm
                    return None

            results = await asyncio.gather(*[prove_one(l) for l in candidates])
            newly = [r for r in results if r]
            for lm in newly:
                proved_bank[lm.name] = lm
            logger.info(f"[Medium] Inner refinement proved {len(newly)} / {len(candidates)} lemmas.")

            # 进入下一次外层循环，用“新上下文”重新 whole proof（Problem with New Context）

        # 超过外层轮数仍未奏效
        return None

    async def heavy_inference(self, statement: str) -> Optional[str]:
        """Heavy推理策略：大规模生成 Lemma（替代原 Conjecture 流程）并尝试证明后用于主定理"""
        logger.info("Starting heavy inference with large-batch lemma generation...")

        # 1) 批量生成大量候选引理
        total_target = 100
        batch_size = 20
        all_lemmas: List[Lemma] = []
        # gen_history/last_text 不再跨批次共享，改为每个批次独立维护
        # 并发限流：避免同时大量占用 LLM 接口
        llm_sem = asyncio.Semaphore(8)

        async def process_batch(batch_idx: int) -> List[Lemma]:
            """生成一个批次的候选引理并在批次内部完成语法修复与兜底。"""
            history: List[Dict[str, str]] = []
            last_text = ""
            # 生成
            async with llm_sem:
                lemmas, history, last_text = await self._generate_lemmas(
                    statement, history=history, num_lemmas=batch_size, is_conjecture=True
                )

            # 批次内语法检查与修复
            ok = False
            max_regen = 6
            for attempt in range(max_regen):
                ok, feedback = await self._check_lemmas_syntax(lemmas)
                if ok:
                    logger.info(f"[batch {batch_idx}] lemma syntax check passed.")
                    break
                logger.warning(f"[batch {batch_idx}] syntax/type errors, repairing... attempt {attempt + 1}/{max_regen}")
                logger.info(f"[batch {batch_idx}] Compiler feedback:\n{feedback}")
                async with llm_sem:
                    lemmas, history, last_text = await self._repair_lemmas(
                        statement, history, feedback, last_text
                    )

            if not ok:
                logger.error(f"[batch {batch_idx}] still fails after multiple repairs. Salvaging individually...")
                salvaged: List[Lemma] = []
                for l in lemmas:
                    single_ok, _ = await self._check_lemmas_syntax([l])
                    if single_ok:
                        salvaged.append(l)
                lemmas = salvaged
                logger.info(f"[batch {batch_idx}] Salvaged {len(lemmas)} syntactically valid lemmas")
            return lemmas

        batch_count = total_target // batch_size
        batch_tasks = [process_batch(i) for i in range(batch_count)]
        batch_results = await asyncio.gather(*batch_tasks)

        for lemmas in batch_results:
            all_lemmas.extend(lemmas)

        # 去重（name 或 statement 任一重复都丢弃）
        seen_names: Set[str] = set()
        seen_statements: Set[str] = set()
        unique_lemmas: List[Lemma] = []
        for l in all_lemmas:
            name = (l.name or "").strip()
            stmt = (l.statement or "").strip()
            if not name or not stmt:
                continue
            if name in seen_names or stmt in seen_statements:
                continue
            seen_names.add(name)
            seen_statements.add(stmt)
            unique_lemmas.append(l)

        logger.info(f"Generated {len(unique_lemmas)} unique lemmas")

        # 3) 并发尝试证明这些引理（和 medium 流程一致）
        proved_lemmas: List[Lemma] = []
        sem = asyncio.Semaphore(80)

        async def prove_lemma_task(lemma: Lemma) -> Optional[Lemma]:
            async with sem:
                lemma_proof = await self.light_inference(lemma.statement, max_rounds=1, max_iterations=8)
                if lemma_proof:
                    lemma.proof = lemma_proof
                    return lemma
            return None

        tasks = [prove_lemma_task(lemma) for lemma in unique_lemmas]
        results = await asyncio.gather(*tasks)
        for pl in results:
            if pl:
                proved_lemmas.append(pl)
                self.lemma_pool.append(pl)

        logger.info(f"Proved {len(proved_lemmas)} out of {len(unique_lemmas)} lemmas")

        # 4) 选择相关引理并证明主命题
        if proved_lemmas:
            relevant_lemmas = await self._select_relevant_lemmas(statement, proved_lemmas, top_k=30)
            final_proof = await self._prove_with_lemmas(statement, relevant_lemmas)
            if final_proof:
                return self._combine_lemmas_and_proof(relevant_lemmas, final_proof)

        return None

    async def _call_llm(self, messages: List[Dict[str, str]], temperature: float) -> Tuple[str, str]:
        """
        调用LLM并实现无限次重试

        Returns:
            Tuple[str, str]: 一个元组，第一个元素是提取出的Lean代码，第二个元素是LLM返回的原始完整内容。
        """
        while True:
            response = await self.client.chat.completions.create(  # 变为真正的异步调用
                model=self.model,
                messages=messages,
                temperature=temperature,
                timeout=3000,
            )
            content = response.choices[0].message.content.strip()
            logger.info("\n[LLM Generated Proof]:\n" + "="*25 + f"\n{content}\n" + "="*25)
            matches = re.findall(r"```(?:lean)?\s*([\s\S]*?)\s*```", content)
            extracted_code = content
            if matches:
                extracted_code = matches[-1].strip()
            return extracted_code, content

    async def _generate_proof(self, statement: str, context: str = "", history: List[Dict[str, str]] = None) -> Tuple[str, List[Dict[str, str]]]:
        """使用LLM生成证明"""
        if history is None:
            history = []

        prompt = f"""You are a Lean 4 theorem prover.
Please first describe and refine a rigorous proof in natural language, and then Return ONE code block for Lean 4.14 starting with `:= by` and ending with a closing ``` that contains a complete proof for the given statement. Your declaration must not use `sorry` or `admit`. You can use tactics like `aesop`, `ring`, `linarith`, `norm_num`, etc. to help you. They are already imported.

Goal:
{statement}

-----
{f"Context and available lemmas:{context}" if context else ""}
"""

        current_messages = history + [{"role": "user", "content": prompt}]
        extracted_code, original_content = await self._call_llm(current_messages, temperature=0.7)

        # 更新历史记录
        new_history = current_messages + [{"role": "assistant", "content": original_content}]

        return extracted_code, new_history

    async def _refine_proof(self, statement: str, proof: str, history: List[Dict[str, str]], skip = False) -> Tuple[bool, str, List[Dict[str, str]]]:
        """基于编译反馈优化证明"""
        async with self.compile_lock:
            # 创建完整的Lean文件
            lean_code = self._create_lean_file(statement, proof)

            logger.info("Compiling Lean code...")
            # 写入文件并编译（放入线程，避免阻塞事件循环）
            success, feedback = await asyncio.to_thread(self.compiler.compile, lean_code)

            if success:
                logger.info("[Compilation Result]: Success")
                return True, proof, history
            else:
                logger.info("[Compilation Result]: Failed")
                logger.error("[Error Message]:\n" + "="*25 + f"\n{feedback}\n" + "="*25)

        if skip:
            return False, proof, history
        
        # 基于反馈生成新的证明
        logger.info("[Refining Proof]...")
        refined_proof, new_history = await self._generate_refined_proof(statement, proof, feedback, history)
        return False, refined_proof, new_history

    async def _generate_refined_proof(self, statement: str, failed_proof: str, error_msg: str, history: List[Dict[str, str]]) -> Tuple[str, List[Dict[str, str]]]:
        """基于错误反馈生成改进的证明"""
        prompt = f"""The following Lean 4 proof failed with an error. Please fix it.
Error message:
{error_msg}
"""

        current_messages = history + [{"role": "user", "content": prompt}]
        extracted_code, original_content = await self._call_llm(current_messages, temperature=0.5)
        new_history = current_messages + [{"role": "assistant", "content": original_content}]
        return extracted_code, new_history

    def _parse_lemmas_from_text(self, content: str) -> List[Lemma]:
        """从文本解析引理列表"""
        lemmas: List[Lemma] = []
        lemma_texts = content.split("---")
        for lemma_text in lemma_texts:
            if "STATEMENT:" in lemma_text:
                name_match = re.search(r"LEMMA_NAME:\s*(.*)", lemma_text, re.DOTALL)
                statement_match = re.search(
                    r"STATEMENT:\s*(?:(?:```(?:lean)?\s*)|`)([\s\S]*?)(?:(?:```)|`)|STATEMENT:\s*([\s\S]*?)(?=DESCRIPTION:|$)",
                    lemma_text
                )
                description_match = re.search(r"DESCRIPTION:\s*(.*)", lemma_text, re.DOTALL)

                name = name_match.group(1).strip().split('\n')[0].strip() if name_match else ""
                statement = (statement_match.group(1) or statement_match.group(2) or "").strip() if statement_match else ""
                description = description_match.group(1).strip().split('\n')[0].strip() if description_match else ""

                if name and statement:
                    lemmas.append(Lemma(name=name, statement=statement, description=description))
        return lemmas

    async def _generate_lemmas(self, statement: str, history: Optional[List[Dict[str, str]]] = None, num_lemmas: int = 10, is_conjecture = False) -> Tuple[List[Lemma], List[Dict[str, str]], str]:
        """生成有用的引理，返回(引理列表, 历史对话, 原始返回文本)"""
        if history is None:
            history = []
        prompt = f"""Given the following Lean 4 theorem statement, 
{"""generate diverse conjectures exploring different aspects like:
- Special cases
- Intermediate results (Important)
- Related inequalities
- Structural properties
- Boundary conditions""" if is_conjecture else "generate useful or key lemmas that would help to prove it."}

Ultimate Goal:
{statement}

Generate {num_lemmas} lemmas in the following format:
LEMMA_NAME: <name>
STATEMENT: <lean4 statement, e.g. (r : ℝ) : Int.floor (r + (1 / 100 : ℝ)) ≤ Int.floor (r + 1). A colon should be included(even at the beginning) if applicable, e.g. : Finset.card (Finset.Icc (19 : ℕ) 91) = 73 >
DESCRIPTION: <brief description>

Separate each lemma with "---". The lemmas should be diverse and explore different aspects of the theorem, and they should be useful for proving the main theorem. The statements should be valid when concatenated like `lemma NAME {{statement}} := by sorry`. Do not include proofs.
The lean version is Lean 4.14.0. Avoid lean3 syntax like `∀`.
"""
        messages = history + [{"role": "user", "content": prompt}]
        _, original = await self._call_llm(messages, temperature=0.8)
        new_history = messages + [{"role": "assistant", "content": original}]
        lemmas = self._parse_lemmas_from_text(original)
        return lemmas, new_history, original

    async def _repair_lemmas(self, statement: str, history: List[Dict[str, str]], compiler_feedback: str, last_lemmas_text: str) -> Tuple[List[Lemma], List[Dict[str, str]], str]:
        """在语法检查失败后，将历史对话和编译报错传回LLM，请其整体修复并重新输出完整引理集"""
        prompt = f"""Your previously proposed lemmas for the goal below failed to type-check in Lean 4.14 when wrapped as `lemma NAME STATEMENT := by sorry`.

Goal:
{statement}

Compiler feedback:
{compiler_feedback}

Please fix all issues and output a complete replacement batch of 5-10 lemmas in EXACTLY this format:

LEMMA_NAME: <name>
STATEMENT: <Lean 4.14 statement, e.g. (r : ℝ) : Int.floor (r + (1 / 100 : ℝ)) ≤ Int.floor (r + 1). A colon should be included if applicable.>
DESCRIPTION: <brief description>

Separate lemmas with '---'.
Requirements:
- Lean 4.14 syntax only (no Lean 3 notations like `∀`).
- Each lemma must type-check as `lemma NAME STATEMENT := by sorry` after importing Mathlib.
- Names must be valid identifiers and unique.
- Do not include any proofs.
"""
        messages = history + [{"role": "user", "content": prompt}]
        _, original = await self._call_llm(messages, temperature=0.4)
        new_history = messages + [{"role": "assistant", "content": original}]
        lemmas = self._parse_lemmas_from_text(original)
        return lemmas, new_history, original

    async def _select_relevant_lemmas(self, statement: str, lemmas: List[Lemma], top_k: int = 20) -> List[Lemma]:
        """选择最相关的引理：由 LLM 排序，失败时回退到基线相似度"""
        # 仅考虑已证明的引理
        proven = [l for l in lemmas if l.proof]
        if not proven:
            return []

        # 构造候选列表，避免超长输入
        max_candidates = 100
        candidates = proven[:max_candidates]

        def build_prompt() -> str:
            items = "\n".join(
                f"- name: {l.name}\n  statement: {l.statement}"
                for l in candidates
            )
            return f"""You are ranking helper for Lean 4 theorem proving.

Goal (theorem statement):
{statement}

Given the following proved lemmas (name + statement), return ONLY a JSON array of lemma names (strings) in descending order of usefulness for proving the goal. Do not include any text outside the JSON array. Do not explain.

Lemmas:
{items}

Constraints:
- Output must be a JSON array of strings, e.g. ["lemma_a","lemma_b",...].
- Include at most {top_k} names.
- Names must come from the provided list exactly.

Example output:
["lemma_name_1", "lemma_name_2", "lemma_name_3"]
"""

        try:
            messages = [{"role": "user", "content": build_prompt()}]
            # 使用原始内容以便解析 JSON
            _, original = await self._call_llm(messages, temperature=0.2)

            # 尝试从原始内容中提取 JSON 数组
            json_str = None
            # 1) 优先匹配代码块中的 JSON
            m = re.search(r"```(?:json)?\s*([\s\S]*?)\s*```", original, re.IGNORECASE)
            if m:
                json_str = m.group(1).strip()
            else:
                # 2) 退化：抓取第一个形如 [ ... ] 的数组
                m2 = re.search(r"\[[\s\S]*\]", original)
                if m2:
                    json_str = m2.group(0)

            ranked_names: List[str] = []
            if json_str:
                parsed = json.loads(json_str)
                if isinstance(parsed, list) and all(isinstance(x, str) for x in parsed):
                    ranked_names = parsed

            # 将名称映射回对象，并保持顺序、去重
            name2lemma = {l.name: l for l in candidates}
            ordered = []
            seen: Set[str] = set()
            for nm in ranked_names:
                if nm in name2lemma and nm not in seen:
                    ordered.append(name2lemma[nm])
                    seen.add(nm)

            # 如果 LLM 返回不足，补齐剩余（使用简单相似度作为兜底）
            if len(ordered) < top_k:
                remaining = [l for l in candidates if l.name not in seen]
                def sim(lm: Lemma) -> float:
                    return len(set(statement.split()) & set(lm.statement.split())) * lm.difficulty
                remaining.sort(key=sim, reverse=True)
                for l in remaining:
                    if len(ordered) >= top_k:
                        break
                    ordered.append(l)

            return ordered[:top_k]

        except Exception as e:
            logger.warning(f"LLM 排序失败，使用基线相似度。原因: {e}")

            # 回退：基于词交集 * 难度
            scored_lemmas: List[Tuple[float, Lemma]] = []
            for lemma in candidates:
                similarity = len(set(statement.split()) & set(lemma.statement.split()))
                score = similarity * lemma.difficulty
                scored_lemmas.append((score, lemma))
            scored_lemmas.sort(key=lambda x: x[0], reverse=True)
            return [lemma for _, lemma in scored_lemmas[:top_k]]

    async def _prove_with_lemmas(self, statement: str, lemmas: List[Lemma], max_retries: int = 8 ) -> Optional[str]:
        """
        使用给定的引理通过 medium_inference 策略来证明命题。
        """
        logger.info(f"Delegating proof with {len(lemmas)} lemmas to medium_inference strategy.")
        # 调用 medium_inference，并将已证明的引理作为初始上下文传入
        return await self.medium_inference(statement, initial_lemmas=lemmas)

    def _combine_lemmas_and_proof(self, lemmas: List[Lemma], main_proof: str) -> str:
        """组合引理和主证明为一个字符串（前置若干 lemma 声明 + 主定理证明片段）。"""
        lemma_proofs = []
        for lemma in lemmas:
            if lemma.proof:
                lemma_proofs.append(f"lemma {lemma.name}{lemma.statement} {lemma.proof}")
        preface = "\n".join(lemma_proofs).strip()
        if preface:
            return preface + "\n\n" + main_proof.strip()
        else:
            return main_proof.strip()

    def _create_lean_file(self, statement: str, proof: str) -> str:
        """创建完整的Lean文件内容。
        允许 `proof` 前面包含若干顶层声明（如 lemma ... := by ...），这些会被放在主定理之前。
        最终文件结构为：头部导入 + 前置声明（可选） + `theorem main_theorem ... := by ...`。
        """
        header = """import Mathlib
import Aesop
import Mathlib.Tactic.Ring
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial
"""
        # 将 proof 拆分为「前置顶层声明」与「主定理证明片段（:= by ...）」。
        preface = ""
        body = proof.strip()
        m = re.search(r"(?s)(.*?)(:=\s*by.*)$", proof)
        if m:
            preface = m.group(1).strip()
            body = m.group(2).strip()

        pieces = [header.rstrip()]
        if preface:
            pieces.append(preface)
        pieces.append(f"theorem main_theorem {statement} {body}")
        return "\n".join(pieces) + "\n"

    def _create_lean_lemmas_file(self, lemmas: List[Lemma]) -> str:
        """创建仅包含引理（用 sorry 证明）的 Lean 文件，用于语法/类型检查"""
        header = """import Mathlib
import Aesop
import Mathlib.Tactic.Ring
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial
"""
        bodies: List[str] = []
        for l in lemmas:
            if not l.name or not l.statement:
                continue
            bodies.append(f"lemma {l.name} {l.statement} := by\n  sorry")
        return header + ("\n\n".join(bodies) + "\n")

    async def _check_lemmas_syntax(self, lemmas: List[Lemma]) -> Tuple[bool, str]:
        """用 sorry 作为证明对一组引理进行语法/类型检查"""
        lean_code = self._create_lean_lemmas_file(lemmas)
        async with self.compile_lock:
            success, feedback = await asyncio.to_thread(self.compiler.compile, lean_code)  # 放入线程
        return success, feedback

async def main():
    """主函数"""
    import sys

    setup_logging()

    # if len(sys.argv) < 2:
    #     logger.info("Usage: python main.py '<lean4_statement>' [strategy]")
    #     sys.exit(1)

    statement = """(r : ℝ) (h₀ : (∑ k in Finset.Icc (19 : ℕ) 91, Int.floor (r + k / 100)) = 546) :
    Int.floor (100 * r) = 743"""  # sys.argv[1]
    strategy = "heavy"  # sys.argv[2] if len(sys.argv) > 2 else "medium"

    # 从环境变量获取API密钥
    api_key = "sk-xxxxxx"  # os.getenv("OPENAI_API_KEY")
    if not api_key:
        logger.error("Please set OPENAI_API_KEY environment variable")
        sys.exit(1)

    prover = SeedProver(api_key)
    proof = await prover.prove(statement, strategy)

    if proof:
        logger.info("✓ Proof found!")
        logger.info(proof)

        # 保存证明到文件
        with open("proved_theorem.lean", "w", encoding='utf-8') as f:
            f.write(prover._create_lean_file(statement, proof))
        logger.info("Proof saved to proved_theorem.lean")
    else:
        logger.info("✗ Failed to find proof")

if __name__ == "__main__":
    asyncio.run(main())