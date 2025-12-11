#!/usr/bin/env python3
"""
Compare results from different tools to ensure they produce the same models/interpretations.

This script:
1. Parses output files from each tool (handling different formats)
2. Extracts models/interpretations
3. Normalizes them to a common format
4. Compares results across tools for the same instance and problem type
5. Reports any discrepancies
"""

import sys
import os
import re
import argparse
from pathlib import Path
from collections import defaultdict
from typing import Dict, Set, Tuple, List, Optional
import ast


def parse_bass_models(content: str, instance_name: str) -> Set[Tuple[int, str]]:
    """Parse BAss output format: f(0) f(1) t(2) u(3) ..."""
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue

        if 'Solution count: 0' in line:
            return None
            
        # Skip log lines and header lines
        if (line.startswith('[') or 
            line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            'Solution count:' in line):
            continue
            
        # Parse model lines: f(0) f(1) t(2) u(3) ...
        # For three-valued semantics, include 'u' values
        if re.match(r'^[ftu]\(\d+\)', line.strip()):
            model = set()
            for match in re.finditer(r'([ftu])\((\d+)\)', line):
                value = match.group(1)  # 'f', 't', or 'u'
                stmt_id = int(match.group(2))
                model.add((stmt_id, value))
            if model:
                models.add(frozenset(model))
    
    return models


def parse_aeon_models(content: str, instance_name: str) -> Set[Tuple[int, str]]:
    """Parse aeon-py output format: {'v_0': False, 'v_1': True, ...}"""
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue
            
        if 'Found 0[nodes:1] fixed-points.' in line:
            return None

        # Skip log lines
        if (line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            line.startswith('Start symbolic') or
            'Found' in line and 'fixed-points' in line):
            continue
            
        # Parse dict lines
        if line.strip().startswith('{') and "'v_" in line:
            try:
                # Parse the dict
                model_dict = ast.literal_eval(line.strip())
                model = set()
                for key, value in model_dict.items():
                    if key.startswith('v_'):
                        stmt_id = int(key[2:])
                        v = None
                        if value == True:
                            v = 't'
                        elif value == False:
                            v = 'f'
                        elif value is None:
                            v = 'u'
                        assert v is not None
                        model.add((stmt_id, v))
                if model:
                    models.add(frozenset(model))
            except:
                pass
    
    return models


def parse_adf_obdd_models(content: str, instance_name: str) -> Set[Tuple[int, str]]:
    """Parse adf-obdd output format: T(0) T(1) F(10) ..."""
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue
            
        # Skip log lines
        if (line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            line.startswith('[')):
            continue
            
        # Parse model lines: T(0) T(1) F(10) ...
        if re.match(r'^[TFu]\(\d+\)', line.strip()):
            model = set()
            for match in re.finditer(r'([TFu])\((\d+)\)', line):
                value = None
                if match.group(1) == 'T':
                    value = 't'
                elif match.group(1) == 'F':
                    value = 'f'
                elif match.group(1) == 'u':
                    value = 'u'
                assert value is not None
                stmt_id = int(match.group(2))
                model.add((stmt_id, value))
            if model:
                models.add(frozenset(model))
    
    # Unfortunately, adf_obdd does not have a clear unsatisfiability indicator
    if len(models) == 0:
        return None

    return models


def parse_k_adf_models(content: str, instance_name: str) -> Set[Tuple[int, str]]:
    """Parse k++ADF output format: f(0) f(1) t(2) ..."""
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue
            
        # Skip log lines
        if (line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            'Adding statements' in line or
            'Initializing' in line or
            'Entering reasoning' in line):
            continue
            
        # Parse model lines: f(0) f(1) t(2) ...
        if re.match(r'^[ftu]\(\d+\)', line.strip()):
            model = set()
            for match in re.finditer(r'([ftu])\((\d+)\)', line):
                value = match.group(1)
                stmt_id = int(match.group(2))
                model.add((stmt_id, value))
            if model:
                models.add(frozenset(model))
    
    # Unfortunately, k-adf does not have a clear unsatisfiability indicator
    if len(models) == 0:
        return None

    return models


def parse_go_diamond_models(content: str, instance_name: str) -> Set[Tuple[int, str]] | None:
    """Parse goDiamond output format: Answer: N followed by f(0) f(1) t(2) ..."""
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue
            
        # Skip log lines
        if (line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            line.startswith('/sw/') or
            line.startswith('========================') or
            'clingo version' in line or
            'Reading from' in line or
            'Solving...' in line or
            'Models' in line or
            'Calls' in line or
            'Time' in line or
            'CPU Time' in line or
            line.startswith('Answer:')):
            continue

        if 'UNSATISFIABLE' in line:
            # Valid empty model set
            return None
    
        # Parse model lines: f(0) f(1) t(2) ...
        if re.match(r'^[ftu]\(\d+\)', line.strip()):
            model = set()
            for match in re.finditer(r'([ftu])\((\d+)\)', line):
                value = match.group(1)
                stmt_id = int(match.group(2))
                model.add((stmt_id, value))
            if model:
                models.add(frozenset(model))
    
    return models


def parse_biolqm_models(content: str, instance_name: str) -> Set[Tuple[int, str]]:
    """Parse bioLQM output format.
    
    For two-valued/preferred: binary strings like 00000000000000000000
    For complete: tree format like "0:  - - - - -    |   1 2" where lines ending with "| @" are complete models
    """
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    var_count = None
    position_to_id = None
    is_complete_format = False
    
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            var_count = None
            position_to_id = None
            is_complete_format = False
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue
            
        # Skip log lines
        if (line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            line.startswith(' WARN') or
            'java -jar' in line):
            continue

        if 'NO RESULTS' in line:
            return None
        
        # Check if this is the complete format (tree format with "NUMBER: values | children/@")
        if re.match(r'^\d+:\s+[-01 ]+\s+\|\s+', line.strip()):
            is_complete_format = True
            
            # Parse tree format: "NUMBER: values | @" or "NUMBER: values | children"
            # Extract the values part (between ":" and "|")
            match = re.match(r'^\d+:\s+(.+?)\s+\|\s+', line.strip())
            if match:
                values_str = match.group(1)
                values = values_str.split()                
                
                # Determine variable count from first complete model line
                if var_count is None:
                    var_count = len(values)
                    position_to_id = get_tsconj_variable_mapping(var_count)
                
                if len(values) == var_count:
                    model = set()
                    for i, val in enumerate(values):
                        var_id = position_to_id[i]
                        if val == '1':
                            value = 't'
                        elif val == '0':
                            value = 'f'
                        elif val == '-':
                            value = 'u'
                        else:
                            continue  # Skip unknown values
                        model.add((var_id, value))
                    if model:
                        models.add(frozenset(model))
            continue
            
        # Parse variable names header: v_0 v_1 v_10 ... (for two-valued/preferred)
        if not is_complete_format and line.strip().startswith('v_') and ' ' in line:
            var_names = []
            for var in line.strip().split():
                if var.startswith('v_'):
                    var_names.append(int(var[2:]))
            var_count = len(var_names)
            position_to_id = get_tsconj_variable_mapping(var_count)
            continue
            
        # Parse binary model lines: 00000000000000000000 (for two-valued/preferred)
        if not is_complete_format and var_count and re.match(r'^[01\- ]+$', line.strip()):
            if ' ' in line:
                binary_str = line.strip().split(' ')
            else:
                binary_str = line.strip()
            if len(binary_str) == var_count:
                model = set()
                for i, bit in enumerate(binary_str):
                    var_id = position_to_id[i]
                    value = None
                    if bit == '1':
                        value = 't'
                    elif bit == '0':
                        value = 'f'
                    elif bit == '-':
                        value = 'u'
                    assert value is not None
                    model.add((var_id, value))
                if model:
                    models.add(frozenset(model))
    
    #print(f"Loaded {len(models)} for {instance_name}")
    return models


def parse_fasp_models(content: str, instance_name: str) -> Set[Tuple[int, str]]:
    """Parse fASP output format: 'v_0': 0, 'v_1': 1, ..."""
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue
            
        # Skip log lines
        if (line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            line.startswith('# ASP')):
            continue

        if 'There are no fixed points.' in line:
            return None
            
        # Parse model lines: 'v_0': 0, 'v_1': 1, ...
        if "'v_" in line and ':' in line:
            try:
                # Try to parse as dict-like string
                model = set()
                for match in re.finditer(r"'v_(\d+)':\s*([01])", line):
                    stmt_id = int(match.group(1))
                    value = 't' if match.group(2) == '1' else 'f'
                    model.add((stmt_id, value))
                if model:
                    models.add(frozenset(model))
            except:
                pass
    
    return models


def parse_mpbn_models(content: str, instance_name: str) -> Set[Tuple[int, str]] | None:
    """Parse mpbn output format: {'v_0': 0, 'v_1': 1, ...} or {'v_0': '*', ...} for preferred"""
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue
            
        # Skip log lines
        if (line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            'set -e' in line or
            '[' in line and '=' in line and ']' in line):  # Skip bash debug lines
            continue
            
        # Parse model lines: {'v_0': 0, 'v_1': 1, ...} or {'v_0': '*', ...}
        if line.strip().startswith('{') and "'v_" in line:
            try:
                # Parse the Python dict using ast.literal_eval
                model_dict = ast.literal_eval(line.strip())
                if isinstance(model_dict, dict):
                    model = set()
                    for key, value in model_dict.items():
                        if key.startswith('v_'):
                            stmt_id = int(key[2:])
                            if value == 0:
                                v = 'f'
                            elif value == 1:
                                v = 't'
                            elif value == '*':
                                v = 'u'  # Undefined for preferred semantics
                            else:
                                continue  # Skip unknown values
                            model.add((stmt_id, v))
                    if model:
                        models.add(frozenset(model))
            except (ValueError, SyntaxError):
                # If parsing fails, try regex fallback
                model = set()
                for match in re.finditer(r"'v_(\d+)':\s*([01\*])", line):
                    stmt_id = int(match.group(1))
                    val = match.group(2)
                    if val == '*':
                        value = 'u'
                    elif val == '1':
                        value = 't'
                    elif val == '0':
                        value = 'f'
                    else:
                        continue
                    model.add((stmt_id, value))
                if model:
                    models.add(frozenset(model))
            except Exception:
                pass
    
    # Check for empty result (no models found)
    if len(models) == 0:
        # Check if this is a valid empty result (instance had no solutions)
        # mpbn doesn't output anything when there are no solutions
        # We can't distinguish between "no output" and "parsing failed", so return empty set
        return None
    
    return models


def get_tsconj_variable_mapping(var_count: int) -> Dict[int, int]:
    """
    Get mapping from tsconj output position to actual variable ID.
    
    tsconj orders variables lexicographically by name (e.g., v_0, v_1, v_10, v_11, v_2, ...),
    so we need to map from position in the binary string to the actual variable ID.
    
    Variables are numbered 0 to var_count-1, sorted lexicographically as strings.
    
    Returns: {position: variable_id}
    """
    # Create list of variable IDs (0 to var_count-1)
    var_ids = list(range(var_count))
    # Sort lexicographically as strings (e.g., "0", "1", "10", "11", "2", ...)
    var_ids_sorted = sorted(var_ids, key=str)
    # Create mapping from position to variable ID
    return {position: var_id for position, var_id in enumerate(var_ids_sorted)}


def parse_tsconj_models(content: str, instance_name: str) -> Set[Tuple[int, str]]:
    """Parse tsconj output format: binary strings like 00000000000000000000"""
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    var_count = None
    position_to_id = None
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            var_count = None
            position_to_id = None
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue
            
        # Skip log lines
        if (line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            '/sw/venv' in line or
            'RuntimeWarning' in line or
            'warnings.warn' in line):
            continue
            
        # Parse binary model lines: 00000000000000000000
        # First binary line determines variable count
        if re.match(r'^[01-]+$', line.strip()):
            binary_str = line.strip()
            if var_count is None:
                var_count = len(binary_str)
                # Compute variable mapping once we know the count
                position_to_id = get_tsconj_variable_mapping(var_count)
            if len(binary_str) == var_count:
                model = set()
                for i, bit in enumerate(binary_str):
                    # Map position to actual variable ID
                    var_id = position_to_id[i]
                    value = None
                    if bit == '1':
                        value = 't'
                    elif bit == '0':
                        value = 'f'
                    elif bit == '-':
                        value = 'u'
                    assert value is not None
                    model.add((var_id, value))
                if model:
                    models.add(frozenset(model))
    
    #print(f"Loaded {len(models)} for {instance_name}")
    return models


def parse_yadf_models(content: str, instance_name: str) -> Set[Tuple[int, str]]:
    """Parse yadf output format: ass(0,0) ass(1,1) ass(2,u) ..."""
    models = set()
    lines = content.split('\n')
    
    in_instance = False
    for line in lines:
        if f"--- Instance: {instance_name} ---" in line:
            in_instance = True
            continue
        if in_instance and line.startswith("--- Instance:"):
            break
        if not in_instance:
            continue
            
        if 'UNSATISFIABLE' in line:
            return None
            
        # Skip log lines
        if (line.startswith('Starting') or 
            line.startswith('Will execute') or
            line.startswith('+') or
            line.startswith('clingo version') or
            'Reading from' in line or
            'Solving...' in line or
            'SATISFIABLE' in line or
            'Models' in line or
            'Calls' in line or
            'Time' in line or
            'CPU Time' in line or
            line.startswith('Answer:') or
            '/sw/' in line or
            'exit_code' in line or
            'case $exit_code' in line or
            'exit 0' in line):
            continue
            
        # Parse model lines: ass(0,0) ass(1,1) ass(2,u) ...
        # Include 'u' for three-valued semantics
        if 'ass(' in line:
            model = set()
            for match in re.finditer(r'ass\((\d+),([01u])\)', line):
                stmt_id = int(match.group(1))
                val = match.group(2)
                if val == 'u':
                    value = 'u'
                else:
                    value = 't' if val == '1' else 'f'
                model.add((stmt_id, value))
            if model:
                models.add(frozenset(model))
    
    return models


# Map tool names to their parsers
PARSERS = {
    'bass': parse_bass_models,
    'aeon': parse_aeon_models,
    'adf_obdd': parse_adf_obdd_models,
    'k_adf': parse_k_adf_models,
    'go_diamond': parse_go_diamond_models,
    'biolqm': parse_biolqm_models,
    'fasp': parse_fasp_models,
    'tsconj': parse_tsconj_models,
    'yadf': parse_yadf_models,
    'mpbn': parse_mpbn_models,
}

# Map problem types to file suffixes
PROBLEM_MAP = {
    '2v': 'two-valued',
    'adm': 'admissible',
    'com': 'complete',
    'prf': 'preferred',
    'stm': 'stable',
}

# Map tool file prefixes to tool names
# Note: Filenames are like "go_diamond_2v.txt", "k_adf_2v.txt", etc.
TOOL_MAP = {
    'bass': 'bass',
    'aeon': 'aeon',
    'adf_obdd': 'adf_obdd',
    'adf': 'adf_obdd',  # Also handle "adf_obdd" split differently
    'k_adf': 'k_adf',
    'k': 'k_adf',  # Also handle "k_adf" split differently
    'go_diamond': 'go_diamond',
    'go': 'go_diamond',  # Also handle "go_diamond" split differently
    'biolqm': 'biolqm',
    'fasp': 'fasp',
    'tsconj': 'tsconj',
    'yadf': 'yadf',
    'mpbn': 'mpbn',
}


def load_results(recorded_dir: Path, problem_type_filter: Optional[str] = None) -> Dict[str, Dict[str, Dict[str, Set]]]:
    """
    Load results from recorded directory.
    
    Args:
        recorded_dir: Directory containing recorded result files
        problem_type_filter: If provided, only load results for this problem type
                           (can be full name like 'two-valued' or short like '2v')
    
    Returns: {problem_type: {tool: {instance: models}}}
    """
    results = defaultdict(lambda: defaultdict(dict))
    
    # Determine which problem suffixes to load
    requested_suffixes = None
    if problem_type_filter:
        # Map to full problem type name
        problem_name_map = {
            '2v': 'two-valued',
            'stm': 'stable',
            'com': 'complete',
            'prf': 'preferred',
            'adm': 'admissible',
        }
        requested_problem = problem_name_map.get(problem_type_filter, problem_type_filter)
        
        # Find all suffixes that map to this problem type
        requested_suffixes = set()
        for suffix, prob_type in PROBLEM_MAP.items():
            if prob_type == requested_problem:
                requested_suffixes.add(suffix)
        # Also include the full name as a suffix (in case some files use it)
        requested_suffixes.add(requested_problem)
    
    for result_file in recorded_dir.glob('*.txt'):
        # Parse filename: tool_problem.txt
        # Handle cases like "go_diamond_2v.txt", "k_adf_2v.txt", "adf_obdd_2v.txt"
        stem = result_file.stem
        
        # Try to match known tool prefixes (longest first)
        tool_name = None
        problem_suffix = None
        
        # Check for multi-part tool names first
        for prefix in ['go_diamond', 'k_adf', 'adf_obdd']:
            if stem.startswith(prefix + '_'):
                tool_name = TOOL_MAP.get(prefix)
                problem_suffix = stem[len(prefix) + 1:]
                break
        
        # If not found, try single-part tool names
        if tool_name is None:
            parts = stem.split('_', 1)
            if len(parts) == 2:
                tool_prefix = parts[0]
                problem_suffix = parts[1]
                tool_name = TOOL_MAP.get(tool_prefix)
        
        if tool_name is None or tool_name not in PARSERS:
            continue  # Skip unknown tools silently
            
        # Filter by problem type if requested
        if requested_suffixes and problem_suffix not in requested_suffixes:
            continue  # Skip files that don't match the requested problem type
        
        problem_type = None
        for suffix, prob_type in PROBLEM_MAP.items():
            if problem_suffix == suffix:
                problem_type = prob_type
                break
        
        if problem_type is None:
            # Try direct mapping
            problem_type = problem_suffix

        print(f"Loading {prob_type} problem for tool {tool_name}")

        # Read file content
        try:
            content = result_file.read_text()
        except Exception as e:
            print(f"Warning: Could not read {result_file}: {e}", file=sys.stderr)
            continue
        
        # Extract instance names from fast files
        # We'll need to find instances by looking for "--- Instance: ... ---" patterns
        instance_pattern = r'--- Instance: ([^-]+) ---'
        instances = set(re.findall(instance_pattern, content))
        
        parser = PARSERS[tool_name]
        for instance in instances:
            instance = instance.strip()
            try:
                models = parser(content, instance)
                if models is None:
                    # Validated empty result
                    results[problem_type][tool_name][instance] = []
                elif len(models) > 0:
                    results[problem_type][tool_name][instance] = models
                else:
                    print(f"Warning: Error parsing {tool_name} {problem_type} {instance}", file=sys.stderr)
            except Exception as e:
                print(f"Warning: Error parsing {tool_name} {problem_type} {instance}: {e}", file=sys.stderr)
                continue
    
    return results


def normalize_model(model: frozenset, problem_type: str) -> Optional[frozenset]:
    """
    Normalize a model for comparison.
    For three-valued semantics, extract only defined parts (t/f, not u).
    For two-valued semantics, return as-is.
    Returns None if model is empty after normalization (all undefined).
    """
    three_valued_semantics = problem_type in ['complete', 'admissible', 'preferred']
    
    if three_valued_semantics:
        # Extract only defined values (t/f), ignore undefined (u)
        normalized = frozenset((stmt_id, value) for stmt_id, value in model if value != 'u')
        return normalized
    else:
        # For two-valued semantics, all values should be t/f
        for _stmt, value in model:
            if value != 't' and value != 'f':
                # Note: This should only happen for tsconj and is a known bug
                return None
        return model


def compare_results(results: Dict[str, Dict[str, Dict[str, Set]]]) -> None:
    """Compare results across tools and report discrepancies."""
    discrepancies = []
    total_compared = 0
    total_matching = 0
    pair_counts = defaultdict(int)  # Count discrepancies per tool pair
    
    for problem_type in sorted(results.keys()):
        tools = results[problem_type]
        if len(tools) < 2:
            continue
        
        # Get all instances that appear in at least one tool
        all_instances = set()
        for tool_results in tools.values():
            all_instances.update(tool_results.keys())
        
        for instance in sorted(all_instances):
            # Get models from each tool for this instance
            tool_models = {}
            for tool_name, tool_results in tools.items():
                if instance in tool_results:
                    tool_models[tool_name] = tool_results[instance]
            
            if len(tool_models) < 2:
                continue
            
            total_compared += 1
            
            # Normalize models for comparison
            normalized_models = {}
            for tool_name, models in tool_models.items():
                normalized = set()
                #empty_count = 0
                for model in models:
                    norm_model = normalize_model(model, problem_type)
                    if norm_model is not None:
                        normalized.add(norm_model)
                    #else:
                    #    empty_count += 1
                # If we have empty models, represent them as a special marker
                # Multiple empty models are equivalent, so we only need one marker
                #if empty_count > 0:
                #    normalized.add(frozenset())  # Empty set represents "all undefined" model
                normalized_models[tool_name] = normalized
            
            # Compare all pairs
            tool_names = sorted(normalized_models.keys())
            all_match = True
            
            for i in range(len(tool_names)):
                for j in range(i + 1, len(tool_names)):
                    tool1, tool2 = tool_names[i], tool_names[j]
                    models1 = normalized_models[tool1]
                    models2 = normalized_models[tool2]
                    
                    if models1 != models2:
                        all_match = False
                        pair_key = (problem_type, tool1, tool2)
                        pair_counts[pair_key] += 1
                        discrepancies.append({
                            'problem': problem_type,
                            'instance': instance,
                            'tool1': tool1,
                            'tool2': tool2,
                            'count1': len(models1),
                            'count2': len(models2),
                            'models1': models1,
                            'models2': models2,
                        })
            
            if all_match:
                total_matching += 1
    
    # Print summary
    print(f"\n=== Comparison Summary ===")
    print(f"Total instances compared: {total_compared}")
    print(f"Instances with matching results: {total_matching}")
    print(f"Instances with discrepancies: {len(discrepancies)}")
    
    # Print discrepancy counts per tool pair
    if pair_counts:
        print(f"\n=== Discrepancy Counts by Tool Pair ===")
        # Group by problem type
        by_problem_pair = defaultdict(lambda: defaultdict(int))
        for (prob_type, tool1, tool2), count in pair_counts.items():
            by_problem_pair[prob_type][(tool1, tool2)] = count
        
        for problem_type in sorted(by_problem_pair.keys()):
            print(f"\n{problem_type.upper()}:")
            pairs = by_problem_pair[problem_type]
            # Sort by count (descending)
            sorted_pairs = sorted(pairs.items(), key=lambda x: x[1], reverse=True)
            for (tool1, tool2), count in sorted_pairs:
                print(f"  {tool1} vs {tool2}: {count} instances")
    
    if discrepancies:
        print(f"\n=== Discrepancies Found ===")
        # Group by problem type for better readability
        by_problem = defaultdict(list)
        for disc in discrepancies:
            by_problem[disc['problem']].append(disc)
        
        for problem_type in sorted(by_problem.keys()):
            print(f"\n--- {problem_type.upper()} ---")
            problem_discs = by_problem[problem_type]
            # Limit output to first 20 discrepancies per problem type
            for disc in problem_discs[:2]:
                print(f"\n  Instance: {disc['instance']}")
                print(f"    {disc['tool1']}: {disc['count1']} models")
                print(f"    {disc['tool2']}: {disc['count2']} models")
                
                # Show differences
                only_in_1 = disc['models1'] - disc['models2']
                only_in_2 = disc['models2'] - disc['models1']
                
                if only_in_1:
                    print(f"    Models only in {disc['tool1']}: {len(only_in_1)}")
                    # Show first 2 examples
                    for model in list(only_in_1)[:20]:
                        model_dict = dict(sorted(model))
                        # Truncate if too long
                        model_str = str(model_dict)
                        if len(model_str) > 100:
                            model_str = model_str[:97] + "..."
                        print(f"      {model_str}")
                
                if only_in_2:
                    print(f"    Models only in {disc['tool2']}: {len(only_in_2)}")
                    # Show first 2 examples
                    for model in list(only_in_2)[:20]:
                        model_dict = dict(sorted(model))
                        # Truncate if too long
                        model_str = str(model_dict)
                        if len(model_str) > 100:
                            model_str = model_str[:97] + "..."
                        print(f"      {model_str}")
            
            if len(problem_discs) > 20:
                print(f"\n  ... and {len(problem_discs) - 20} more discrepancies for {problem_type}")
        
        print(f"\n=== Notes ===")
        print("Some discrepancies may be due to:")
        print("  - Different output formats (full vs partial models)")
        print("  - Tools outputting only defined statements vs all statements")
        print("  - Three-valued vs two-valued representation differences")
        print("  - Parsing limitations for certain tool formats")
        print("\nFor detailed analysis, check the actual result files.")
    else:
        print("\n✓ All tools produced identical results!")


def main():
    parser = argparse.ArgumentParser(
        description='Compare results from different ADF solver tools',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Problem types:
  - two-valued (2v): Two-valued models
  - stable (stm): Stable models
  - complete (com): Complete models
  - preferred (prf): Preferred models
  - admissible (adm): Admissible models

Examples:
  %(prog)s                    # Compare all problem types
  %(prog)s --problem two-valued  # Compare only two-valued results
  %(prog)s -p stable         # Compare only stable results
        """
    )
    parser.add_argument(
        '-p', '--problem',
        choices=['two-valued', 'stable', 'complete', 'preferred', 'admissible', '2v', 'stm', 'com', 'prf', 'adm'],
        help='Problem type to compare (if not specified, all problem types are compared)'
    )
    
    args = parser.parse_args()
    
    script_dir = Path(__file__).parent
    recorded_dir = script_dir / 'results' / 'recorded'
    
    if not recorded_dir.exists():
        print(f"Error: Directory {recorded_dir} does not exist", file=sys.stderr)
        sys.exit(1)
    
    # Load results, filtering by problem type if specified
    if args.problem:
        print(f"Loading results for problem type: {args.problem}...")
        results = load_results(recorded_dir, problem_type_filter=args.problem)
        
        # Map short names to full names for display
        problem_name_map = {
            '2v': 'two-valued',
            'stm': 'stable',
            'com': 'complete',
            'prf': 'preferred',
            'adm': 'admissible',
        }
        requested_problem = problem_name_map.get(args.problem, args.problem)
        
        if not results or requested_problem not in results:
            print(f"Error: No results found for problem type '{requested_problem}'", file=sys.stderr)
            sys.exit(1)
    else:
        print("Loading results from recorded files...")
        results = load_results(recorded_dir)
    
    print(f"\nLoaded results for {len(results)} problem type(s)")
    for prob_type, tools in results.items():
        print(f"  {prob_type}: {len(tools)} tools ({sorted(tools.keys())})")
    
    print("\nComparing results...")
    compare_results(results)


if __name__ == '__main__':
    main()
