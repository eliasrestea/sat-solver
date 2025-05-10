import time
from typing import Set, List, Dict, Tuple, OrderedDict
import re
import io
import sys
from dataclasses import dataclass
from typing import Optional
from itertools import product, combinations
from collections import OrderedDict

DUAL_OPERATORS = {'|', '&', '>', '=', '^'}
SINGLE_OPERATORS = {'-'}
AVAILABLE_LETTERS = set('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789αβγδεζηικλμξπρσςτυφχψω')

def custom_key(char):
    custom_order = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789αβγδεζηικλμξπρσςτυφχψω"
    order_map = {char: index for index, char in enumerate(custom_order)}
    return order_map[char]

logical_equivalences = {
    # Reduction Laws
    "(A=B)": "(((-A)|B)&((-B)|A))",
    "(A>B)": "((-A)|B)",

    "(A&B&C)|(A&B&(-C))": "((A&B)&(C|(-C)))",
    "(A&(-B)&C)|((-A)&B&C)": "(((A &(-B))|((-A)&B))&C)",
    "((-A)&B&C)|(A&(-B)&C)": "(((A &(-B))|((-A)&B))&C)",
    "((A&B)&⊤)": "(A&B)",
    # Laws for Tautology (⊤) and Contradiction (⊥)
    "(-⊤)": "⊥",
    "(-⊥)": "⊤",
    "(A|⊥)": "A",
    "(A&⊤)": "A",
    "(A|⊤)": "⊤",
    "(A&⊥)": "⊥",
    "(⊥>A)": "⊤",
    "(A>⊤)": "⊤",

    # Idempotent Laws
    "(A&A)": "A",
    "(A|A)": "A",

    # Absorption Laws
    "(A|(A&B))": "A",
    "(A&(A|B))": "A",

    # Annihilation Laws
    "(A|(-A))": "⊤",  # Law of Excluded Middle
    "((-A)|A)": "⊤",  # Law of Excluded Middle
    "(A&(-A))": "⊥",
    "(A>A)": "⊤",
    "(P&Q&(-P))": "⊥",
    "((-P)&Q&P)": "⊥",
    "(Q&P&(-P))": "⊥",
    "(Q&(-P)&P)": "⊥",
    "((-P)&P)": "⊥",
    "(P|Q|(-Q))": "⊤",

    # Negation Laws
    "(-(-A))": "A",
    "(-(A|B))": "((-A)&(-B))",  # De Morgan's Law for Disjunction
    "(-(A&B))": "((-A)|(-B))",  # De Morgan's Law for Conjunction
    "(-(A>B))": "(A|(-B))",
    "(-(A=B))": "(A=(-B))",
    "(P&(Q&(-P)))": "⊥",
    "(P&((-P)&Q))": "⊥",
    "(Q&(P&(-P)))": "⊥",
    "(Q&((-P)&P))": "⊥",
    "(P|(Q|(-P)))": "⊤",
    "(P|((-P)|Q))": "⊤",
    "(Q|(P|(-P)))": "⊤",
    "(Q|((-P)|P))": "⊤",
}
def is_custom_alpha(char: str) -> bool:
    """Check if a character is alphabetic, including additional characters."""
    additional_alpha = AVAILABLE_LETTERS
    return True if char in additional_alpha else False

def _get_all_variables(expression: str) -> list:
    """Get all unique propositional variables from a logical expression in their order of appearance."""
    seen = set()
    variables = []
    for char in expression:
        if is_custom_alpha(char) and char not in seen:
            variables.append(char)
            seen.add(char)
    return variables


def simplify_nested_expression(expression):
    # Remove outer parentheses
    expression = expression.strip('()')
    operator = ''
    for character in expression:
        if character in DUAL_OPERATORS:
            operator = character
    elements = expression.split(operator)

    # Base case for one element
    if len(elements) <= 1:
        return expression

    # Start building the nested structure
    nested_expr = elements[-2] + operator + elements[-1]
    for i in range(len(elements) - 3, -1, -1):
        nested_expr = elements[i] + f'{operator}(' + nested_expr + ')'
    print()
    # Return the nested expression with outer parentheses
    print(f"Subformula: {expression} is equivalent to {nested_expr}")
    return f'({nested_expr})'

def logical_equivalence(expression: str):
    """Replace variables in the logical_equivalences dict with new placeholders."""
    variables = _get_all_variables(expression)
    placeholders = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z']
    replacements = {}

    # Create a mapping of each variable to a unique placeholder
    for var in variables:
        if var in placeholders:
            available_letters = AVAILABLE_LETTERS - set(placeholders) - set(variables)
            new_placeholder = min(available_letters, key=custom_key)
            placeholders[placeholders.index(var)] = new_placeholder
            replacements[var] = new_placeholder

    # Replace variables in the logical_equivalences dictionary
    updated_logical_equivalences = {}
    for key, value in logical_equivalences.items():
        new_key = key
        new_value = value
        for var, new_placeholder in replacements.items():
            new_key = new_key.replace(var, new_placeholder)
            new_value = new_value.replace(var, new_placeholder)
        updated_logical_equivalences[new_key] = new_value
    variable_map = {placeholders[i]: var for i, var in enumerate(variables)}
    def replace_placeholders(equivalence: str) -> str:
        for placeholder, variable in variable_map.items():
            equivalence = equivalence.replace(placeholder, variable)
        return equivalence
    updated_equivalences = {replace_placeholders(k): replace_placeholders(v) for k, v in updated_logical_equivalences.items()}
    if updated_equivalences.get(expression):
        return True, updated_equivalences.get(expression, expression)
    return False, False

class WFFValidator:
    """A validator for Well-Formed Formulas (WFF) in propositional logic."""

    def __init__(self, wff_processor):

        self.processor = wff_processor
        self.old_expression = wff_processor.expression
        self.is_validated = None
        self.used_letters: Set[str] = set()
        self.replacements = {}
        self.variables = set(_get_all_variables(wff_processor.expression))

    def find_smallest_group(self) -> str:
        """Find the smallest well-formed group within parentheses.

        Returns:
            str: The smallest complete group found, or empty string if none found
        """
        stack = []
        min_length = float('inf')
        min_group = ''
        if len(self.processor.expression)==1:
            return self.processor.expression
        for i, char in enumerate(self.processor.expression):
            if char == '(':
                stack.append(i)
            elif char == ')' and stack:
                start = stack.pop()
                group = self.processor.expression[start:i + 1]
                if group.count('(') == group.count(')'):
                    if len(group) < min_length:
                        min_length = len(group)
                        min_group = group

        return min_group

    def is_wff(self, formula: str) -> bool:
        """Check if a formula is well-formed with a single consistent connective.

        Args:
            formula (str): The formula to check

        Returns:
            bool: True if the formula is well-formed, False otherwise
        """
        # Single letter case
        if len(formula) == 1:
            print(f"{formula} is a WFF")
            return True
        elif len(formula) == 0:
            print(f"{formula} is not a WFF")
            return False

        # Check if it's a properly parenthesized expression
        if not (formula[0] == '(' and formula[-1] == ')'):
            print(f"{formula} is not a WFF")
            return False

        inner = formula[1:-1]  # Remove outer parentheses
        if '(' in inner or ')' in inner:
            print(f"{formula} is not a WFF")
            return False

        # Check for unary operators: (-P) or (~P)
        if inner[0] in SINGLE_OPERATORS and len(inner) == 2:
            is_valid = is_custom_alpha(inner[1])
            print(f"{formula} {'is' if is_valid else 'is not'} a WFF")
            return is_valid

        # Split the inner formula into components
        components = []
        current = ""
        connective = None
        for char in inner:
            if char in DUAL_OPERATORS:
                if current:
                    components.append(current)

                # Check if we already have a connective and this one is different
                if connective and char != connective:
                    print(f"{formula} is not a WFF (mixed connectives)")
                    return False

                connective = char
                components.append(char)
                current = ""
            else:
                current += char
        if current:
            components.append(current)

        # Check if we have alternating variables and operators
        if len(components) < 3:
            print(f"{formula} is not a WFF")
            return False

        # Check pattern: letter operator letter (operator letter)*
        for i in range(len(components)):
            if i % 2 == 0:  # Should be a letter
                if not is_custom_alpha(components[i]) or len(components[i]) != 1:
                    print(f"{formula} is not a WFF")
                    return False
            else:  # Should be an operator
                if components[i] not in DUAL_OPERATORS or components[i] != connective:
                    print(f"{formula} is not a WFF")
                    return False

        print(f"{formula} is a WFF")
        if len(formula) > 5:
            replacement = simplify_nested_expression(formula)
            print(f"Subformula: {formula} is equivalent to {replacement}, replacing...")
            self.replacement_needed(formula, replacement)
        return True

    def replace_wff(self, small_formula: str) -> None:
        """Replace a well-formed formula with a single letter.

        Args:
            small_formula (str): The formula to replace
        """
        # Find an unused replacement letter
        available_letters = AVAILABLE_LETTERS - self.used_letters - self.variables
        if not available_letters:
            raise ValueError("No more available letters for replacement")
        reversed_replacements = {v: k for k, v in self.replacements.items()}
        if small_formula in reversed_replacements:
            replacement = reversed_replacements[small_formula]
        else:
            replacement = min(available_letters, key=custom_key)
        self.used_letters.add(replacement)

        # Replace the first occurrence of the small formula
        self.processor.expression = self.processor.expression.replace(small_formula, replacement, 1)
        self.replacements[replacement] = small_formula
        print(f"{small_formula} := {replacement}")

    def validate(self) -> bool:
        """Validate the entire expression.

        Returns:
            bool: True if the entire expression is a well-formed formula
        """
        print(f"Initial string: {self.processor.expression}")
        self.old_expression = self.processor.expression

        while True:
            # Find and validate the smallest group
            smallest_group = self.find_smallest_group()

            if not self.is_wff(smallest_group) or not smallest_group:
                print("String is not a WFF")
                self.is_validated = False
                return False

            self.replace_wff(smallest_group)
            print(f"String is now: {self.processor.expression}")

            # Check if we're done
            if len(self.processor.expression) == 1 and self.is_wff(self.processor.expression):
                print("String is a WFF")
                self.is_validated = True
                self.processor.expression = self.old_expression
                self.used_letters.clear()
                self.replacements.clear()
                return True

    def replacement_needed(self, formula: str, replacement: str):
        needed = True
        while needed:
            needed = False
            for key in self.replacements:
                if key in formula or key in replacement:
                    needed = True
                formula = formula.replace(key, self.replacements[key])
                replacement = replacement.replace(key, self.replacements[key])
        self.old_expression = self.old_expression.replace(formula, replacement)
        self.replacements[formula] = replacement

    def simplify_formula(self):
        """Simplify the formula."""
        text_trap = io.StringIO()
        sys.stdout = text_trap
        self.validate()
        sys.stdout = sys.__stdout__
        if not self.is_validated:
            print(f"Expression is not a valid WFF {self.processor.expression}")
            return

        self.old_expression = self.processor.expression

        while True:
            # Find and validate the smallest group
            text_trap = io.StringIO()
            sys.stdout = text_trap
            smallest_group = self.find_smallest_group()
            self.replace_wff(smallest_group)
            sys.stdout = sys.__stdout__
            one_variable_groups = 0
            if len(self.processor.expression) == 1:
                for i in self.replacements:
                    if len(_get_all_variables(self.replacements[i])) == 1:
                        one_variable_groups += 1
                smallest_group = self.processor.expression
                tried_all = []
                if len(smallest_group) > 5 and "(" not in smallest_group[1:-1] and ")" not in smallest_group[1:-1]:
                    replacement = simplify_nested_expression(smallest_group)
                    self.replacement_needed(smallest_group, replacement)
                    self.processor.expression = self.old_expression
                    return self.simplify_formula()
                else:
                    needed = True
                    while needed:
                        needed = False
                        truth, replacement = logical_equivalence(smallest_group)
                        if truth:
                            self.replacement_needed(smallest_group, replacement)
                            self.processor.expression = self.old_expression
                            return self.simplify_formula()
                        else:
                            for key in self.replacements:
                                if key in smallest_group:
                                    needed = True
                                    smallest_group = smallest_group.replace(key, self.replacements[key])
                                    break
                        if not needed and len(tried_all) != one_variable_groups:
                            needed = True
                            for key in self.replacements:
                                if key not in tried_all and len(_get_all_variables(self.replacements[key])) == 1:
                                    tried_all.append(key)
                                    smallest_group = key
                                    break


                print("Simplified to ", self.old_expression)
                self.is_validated = True
                self.processor.expression = self.old_expression
                self.used_letters.clear()
                self.replacements.clear()
                return True


@dataclass
class Node:
    """Represents a node in the syntax tree."""
    label: str
    left: Optional['Node'] = None
    right: Optional['Node'] = None
    is_open: bool = False  # For "F" nodes
    is_current: bool = False  # For current position
    is_connective_open: bool = False  # For "□" nodes or "-" waiting to be filled


class WFFTree:
    """Builds a tree representation of a Well-Formed Formula (WFF)."""

    def __init__(self, wff_processor):
        self.processor = wff_processor
        self.current_node = None
        self.root = None
        self.step_count = 0
        self.finished = False

    def display_tree(self, node: Optional[Node], level: int = 0, is_right: bool = True) -> List[str]:
        """Creates a string representation of the tree."""
        if not node:
            return []

        # Prepare the node label
        label = node.label
        if node.is_open:
            label = '"F"'
        elif node.is_connective_open:
            if node.label == '-':
                label = '"-"'
            else:
                label = '"□"'

        if node.is_current:
            label = f'[{label}]'  # Mark current position with interrupted outline

        # Calculate indentation
        indent = "    " * level
        prefix = indent + ("└── " if is_right else "├── ")

        # Build the tree lines
        lines = [prefix + label]
        if node.left:
            lines.extend(self.display_tree(node.left, level + 1, False))
        if node.right:
            lines.extend(self.display_tree(node.right, level + 1, True))

        return lines

    def find_parent(self, node: Node, target: Node) -> Optional[Node]:
        """Find the parent node of a given target node."""
        if not node:
            return None
        if node.left is target or node.right is target:
            return node
        left_result = self.find_parent(node.left, target)
        if left_result:
            return left_result
        return self.find_parent(node.right, target)

    def handle_open_parenthesis(self, next_symbol: str) -> bool:
        """Handle an open parenthesis by creating both possible structures."""
        if not self.current_node or not self.current_node.is_open:
            return False

        # Create both possible structures as per lecture notes
        # Structure 1: Negation
        neg_structure = Node('-',
                             right=Node(label='F', is_open=True),
                             is_connective_open=True)

        # Structure 2: Binary operator
        bin_structure = Node('□',
                             left=Node(label='F', is_open=True),
                             right=Node(label='F', is_open=True),
                             is_connective_open=True)

        # Determine which structure to use based on the next symbol
        selected_structure = neg_structure if next_symbol in SINGLE_OPERATORS else bin_structure

        # Update the tree structure
        if self.current_node is self.root:
            self.root = selected_structure
        else:
            parent = self.find_parent(self.root, self.current_node)
            if parent.left is self.current_node:
                parent.left = selected_structure
            else:
                parent.right = selected_structure

        # Move current position to first component based on selected structure
        self.current_node.is_current = False
        if next_symbol in SINGLE_OPERATORS:
            # For neg_structure, the left child becomes the new current node
            neg_structure.is_current = True
            self.current_node = neg_structure
        else:
            # For bin_structure, the left child becomes the new current node
            bin_structure.left.is_current = True
            self.current_node = bin_structure.left

        return True

    def handle_close_parenthesis(self) -> bool:
        """Handle a closing parenthesis by moving up the tree."""
        if not self.current_node:
            return False

        parent = self.find_parent(self.root, self.current_node)
        if parent:
            self.current_node.is_current = False
            parent.is_current = True
            self.current_node = parent
        else:
            self.current_node.is_current = False
            self.current_node = None

        return True

    def handle_operator(self, operator: str) -> bool:
        """Handle logical operators (-, &, |, >, =, ^)."""
        if not self.current_node or not hasattr(self.current_node, 'is_connective_open'):
            return False
        if self.current_node and self.current_node.is_connective_open:
            self.current_node.is_connective_open = False
            self.current_node.label = operator
            self.current_node.is_current = False
            if operator in SINGLE_OPERATORS:
                self.current_node.right.is_current = True
                self.current_node = self.current_node.right
            elif operator in DUAL_OPERATORS:
                self.current_node.right.is_current = True
                self.current_node = self.current_node.right
            return True

        return False

    def handle_variable(self, variable: str) -> bool:
        """Handle propositional variables."""
        if not self.current_node or not self.current_node.is_open:
            return False

        self.current_node.label = variable
        self.current_node.is_open = False

        parent = self.find_parent(self.root, self.current_node)
        if parent:
            self.current_node.is_current = False
            parent.is_current = True
            self.current_node = parent
        else:
            self.current_node.is_current = False
            self.current_node = None

        return True

    def print_step(self, symbol: str, description: str):
        """Print the current step in the parsing process."""
        self.step_count += 1
        print(f"\nStep {self.step_count}: Processing symbol '{symbol}'")
        print(f"Action: {description}")
        print("Current tree:")
        tree_lines = self.display_tree(self.root, 0)
        print("\n".join(tree_lines))
        print("-" * 50)

    def parse(self) -> bool:
        """Parse the input formula and build the syntax tree."""
        # Start with a single open node
        self.root = Node(label='F', is_open=True, is_current=True)
        self.current_node = self.root
        self.step_count = 0
        tree_lines = self.display_tree(self.root, 0)
        print("\n".join(tree_lines))
        # Process each symbol
        for i, symbol in enumerate(self.processor.expression):
            if symbol.isspace():
                continue

            success = True
            if symbol == '(':
                success = self.handle_open_parenthesis(self.processor.expression[i + 1])
                description = "Creating both possible structures and finding the right one"
            elif symbol == ')':
                success = self.handle_close_parenthesis()
                description = "Moving current position up"
            elif symbol in DUAL_OPERATORS or symbol in SINGLE_OPERATORS:
                success = self.handle_operator(symbol)
                description = f"Placing operator {symbol}"
            elif is_custom_alpha(symbol):
                success = self.handle_variable(symbol)
                description = f"Placing variable {symbol}"
            else:
                success = False
                description = f"Invalid symbol {symbol}"

            self.print_step(symbol, description)

            if not success:
                print(f"Parsing failed at symbol: {symbol}")
                return False

        # Check if we have a complete tree
        is_complete = (
                self.current_node is None and
                not any(node.is_open or node.is_connective_open
                        for node in self._get_all_nodes(self.root))
        )

        if is_complete:
            self.finished = True
            print("\nParsing successful! Final tree:")
        else:
            print("\nParsing incomplete. Final tree:")

        tree_lines = self.display_tree(self.root, 0)
        print("\n".join(tree_lines))
        return is_complete

    def _get_all_nodes(self, node: Node) -> List[Node]:
        """Helper function to get all nodes in the tree."""
        if not node:
            return []
        return [node] + self._get_all_nodes(node.left) + self._get_all_nodes(node.right)

@dataclass
class SubFormula:
    """Represents a subformula in the expression."""
    expression: str
    node: Node

class SubFormulas:

    def __init__(self, wff_processor):
        self.processor = wff_processor
        self.dict: OrderedDict[str, Node] = OrderedDict()

    def _collect(self, node: Node, parent_op: str = '') -> str:
        """Recursively collect all subformulas from the tree."""
        if not node:
            return ''

        # Base case: single variable
        if len(node.label) == 1 and is_custom_alpha(node.label):
            return node.label

        # Build subformulas recursively
        if node.label == '-':
            right_expr = self._collect(node.right, node.label)
            expr = f"({node.label}{right_expr})"
            self.dict[expr] = node
            return expr

        if node.label in DUAL_OPERATORS:
            left_expr = self._collect(node.left, node.label)
            right_expr = self._collect(node.right, node.label)
            expr = f"({left_expr}{node.label}{right_expr})"
            self.dict[expr] = node
            return expr

        return ''

class WFFTruthTable:
    """Generates and displays truth tables for Well-Formed Formulas with intermediate steps."""

    def __init__(self, wff_processor):
        self.processor = wff_processor
        self.variables: Set[str] = set()
        self.subformulas = SubFormulas(wff_processor)

    def _evaluate_subformula(self, node: Node, values: Dict[str, bool]) -> bool:
        """Recursively evaluate a subformula represented by a node."""
        if not node:
            return False

        # Base case: single variable
        if len(node.label) == 1 and is_custom_alpha(node.label):
            return values[node.label]

        # Negation case
        if node.label == '-':
            return not self._evaluate_subformula(node.right, values)

        # Binary operators
        left_val = self._evaluate_subformula(node.left, values)
        right_val = self._evaluate_subformula(node.right, values)

        if node.label == '|':
            return left_val or right_val
        elif node.label == '&':
            return left_val and right_val
        elif node.label == '>':
            return (not left_val) or right_val
        elif node.label == '^':
            return left_val != right_val
        elif node.label == '=':
            return left_val == right_val

        return False

    def generate_table(self) -> Tuple[List[str], List[List[bool]], Dict[str, List[bool]]]:
        """Generate the truth table for the formula including intermediate results."""
        # Validate the formula first
        if self.processor.validator_simplificator.is_validated is None:
            self.processor.validate_expression()

        if not self.processor.validator_simplificator.is_validated:
            raise ValueError("Expression is not a valid WFF")

        # Collect all subformulas
        self.subformulas._collect(self.processor.tree.root)

        # Get variables and generate truth value combinations
        self.variables = _get_all_variables(self.processor.expression)
        var_list = sorted(list(self.variables))
        combinations = list(product([False, True], repeat=len(self.variables)))

        # Generate truth values for each combination
        value_rows = []
        subformula_results = {expr: [] for expr in self.subformulas.dict.keys()}

        for combo in combinations:
            # Create variable assignment dictionary
            values = dict(zip(var_list, combo))
            value_rows.append(list(combo))

            # Evaluate each subformula for this combination
            for expr, node in self.subformulas.dict.items():
                result = self._evaluate_subformula(node, values)
                subformula_results[expr].append(result)
        return var_list, value_rows, subformula_results

    def display_table(self) -> None:
        """Display the truth table with intermediate results in a formatted manner."""
        try:
            variables, rows, subformula_results = self.generate_table()
        except ValueError as e:
            print(f"Error: {e}")
            return

        # Calculate column widths
        var_width = max(len(var) for var in variables)
        subformula_width = max(len(expr) for expr in self.subformulas.dict.keys())
        col_width = max(var_width, subformula_width, 5)  # minimum 5 characters

        # Prepare headers
        headers = variables + list(self.subformulas.dict.keys())

        # Print header row
        header = ' | '.join(h.center(col_width) for h in headers)
        print('-' * len(header))
        print(header)
        print('-' * len(header))

        # Print truth table rows
        for i, row in enumerate(rows):
            # Format variable values
            values = [str(int(v)).center(col_width) for v in row]

            # Add subformula results
            for results in subformula_results.values():
                values.append(str(int(results[i])).center(col_width))

            print(' | '.join(values))

        print('-' * len(header))

class WFFProcessor:
    """A processor for Well-Formed Formulas (WFF) in propositional logic."""

    def __init__(self, expression: str):
        self.expression = expression
        self.validator_simplificator = WFFValidator(self)
        self.tree = WFFTree(self)
        self.truth_table = WFFTruthTable(self)

    def validate_expression(self):
        """Validate the expression using the validator."""
        self.validator_simplificator.validate()

    def get_tree(self):
        """Display the interpretation of a WFF."""
        if self.validator_simplificator.is_validated is None:
            text_trap = io.StringIO()
            sys.stdout = text_trap
            self.validator_simplificator.validate()
            sys.stdout = sys.__stdout__
        elif not self.validator_simplificator.is_validated:
            print("Expression is not a WFF, cannot generate tree.")
            return
        self.tree.parse()

    def generate_truth_table(self):
        """Generate and display the truth table."""
        if self.validator_simplificator.is_validated is None:
            text_trap = io.StringIO()
            sys.stdout = text_trap
            self.validator_simplificator.validate()
            sys.stdout = sys.__stdout__
        if not self.tree.finished:
            text_trap = io.StringIO()
            sys.stdout = text_trap
            self.tree.parse()
            sys.stdout = sys.__stdout__
        if not self.validator_simplificator.is_validated:
            print("Expression is not a WFF, cannot generate truth table.")
            return

        self.truth_table.display_table()

    def silent_validator_and_tree_and_table(self, expression: str, processor):
        """Validate the expression using the validator."""
        text_trap = io.StringIO()
        sys.stdout = text_trap
        self.expression = expression
        is_valid = self.validator_simplificator.validate()
        self.tree.parse()
        sys.stdout = sys.__stdout__
        if not is_valid:
            print("Expression is not a WFF.")
            return False, False, False
        variables, rows, subformula_results = WFFTruthTable(processor).generate_table()
        WFFTruthTable(processor).display_table()
        return variables, rows, subformula_results

    def simplify_formula(self):
        """Simplify the formula."""
        print(f"Simplifying formula: {self.expression}")

        self.validator_simplificator.simplify_formula()

    def resolution(self):
        """Check if the formula is unsatisfiable using resolution (with step-by-step output)."""

        a, b, results = self.silent_validator_and_tree_and_table(self.expression, self)
        clauses = []

        print("=== Resolution Step-by-Step ===")
        for key in results:
            # Skip compound formulas (contain '&')
            if '&' in key:
                continue
            inner = key[1:-1] if key.startswith('(') and key.endswith(')') else key
            literals = re.findall(r'-?[A-Z]', inner)
            if literals:
                clause = set(literals)
                clauses.append(clause)

        # Helper function to format clauses for cleaner output
        def format_clause(clause):
            """Format a clause for clean printing without Python's set syntax."""
            return "{" + ", ".join(sorted(clause)) + "}"

        print("\nInitial clauses:")
        for i, clause in enumerate(clauses):
            print(f"C{i + 1}: {format_clause(clause)}")

        def resolution_algorithm(clauses):
            """Apply resolution and print steps."""
            new = set()

            def complementary(lit):
                return lit[1:] if lit.startswith('-') else '-' + lit

            clauses = set(frozenset(c) for c in clauses)
            clause_list = list(clauses)
            clause_ids = {frozenset(c): f"C{i + 1}" for i, c in enumerate(clause_list)}
            clause_counter = len(clause_list) + 1

            while True:
                pairs = [(ci, cj) for i, ci in enumerate(clause_list)
                         for j, cj in enumerate(clause_list) if i < j]

                new_generated = False

                for ci, cj in pairs:
                    for lit in ci:
                        comp = complementary(lit)
                        if comp in cj:
                            resolvent = (ci - {lit}) | (cj - {comp})
                            if not resolvent:
                                print(
                                    f"\nDerived empty clause from {clause_ids[frozenset(ci)]} and {clause_ids[frozenset(cj)]} by resolving on '{lit}' and '{comp}'")
                                print("❌ Contradiction! Formula is UNSATISFIABLE")
                                return True
                            new_clause = frozenset(resolvent)
                            if new_clause not in clauses and new_clause not in new:
                                clause_name = f"C{clause_counter}"
                                print(f"\n{clause_name}: {format_clause(resolvent)}")
                                print(f"  from {clause_ids[frozenset(ci)]} = {format_clause(ci)}")
                                print(f"   and {clause_ids[frozenset(cj)]} = {format_clause(cj)}")
                                print(f"  by resolving on '{lit}' and '{comp}'")
                                clause_ids[new_clause] = clause_name
                                clause_counter += 1
                                new.add(new_clause)
                                new_generated = True

                if not new_generated:
                    print("\n✅ No new clauses generated. Formula is SATISFIABLE (no contradiction found)")
                    return False

                clauses |= new
                clause_list = list(clauses)

        result = resolution_algorithm(clauses)
        return result

    def dpll(self):
        """Check if the formula is satisfiable using DPLL algorithm with step-by-step output."""

        a, b, results = self.silent_validator_and_tree_and_table(self.expression, self)
        clauses = []

        print("=== DPLL Step-by-Step ===")

        for key in results:
            # Skip compound formulas (contain '&')
            if '&' in key:
                continue

            inner = key[1:-1] if key.startswith('(') and key.endswith(')') else key
            literals = re.findall(r'-?[A-Z]', inner)
            if literals:
                clause = set(literals)
                clauses.append(clause)

        # Helper function to format clauses for cleaner output
        def format_clause(clause):
            """Format a clause for clean printing."""
            if not clause:
                return "∅"  # Empty set symbol
            return "{" + ", ".join(sorted(clause)) + "}"

        print("\nInitial clauses:")
        for i, clause in enumerate(clauses):
            print(f"C{i + 1}: {format_clause(clause)}")

        # Extract all variables from the formula
        variables = set()
        for clause in clauses:
            for lit in clause:
                var = lit[1:] if lit.startswith('-') else lit
                variables.add(var)

        # Convert to list and sort for deterministic behavior
        variables = sorted(list(variables))

        print(f"\nVariables: {', '.join(variables)}")

        # Create a copy of clauses for manipulation
        formula = [set(c) for c in clauses]

        # Initialize assignment dictionary
        assignment = {}

        # Counter for tracking decision levels
        decision_level = 0

        def unit_propagation(formula, assignment, level):
            """Apply unit propagation and return (updated_formula, updated_assignment, conflict)."""
            changed = True
            propagation_count = 0

            while changed:
                changed = False
                # Find unit clauses
                unit_clauses = []
                for clause in formula:
                    if len(clause) == 1:
                        unit_clauses.append(list(clause)[0])

                for unit in unit_clauses:
                    var = unit[1:] if unit.startswith('-') else unit
                    value = not unit.startswith('-')

                    # Check for conflict
                    if var in assignment and assignment[var][0] != value:
                        opposite_level = assignment[var][1]
                        print(
                            f"  ❌ Conflict: Variable {var} assigned both True and False (levels {opposite_level} and {level})")
                        return formula, assignment, True

                    if var not in assignment:
                        propagation_count += 1
                        changed = True
                        assignment[var] = (value, level)
                        print(f"  Unit propagation: {var} = {value} (from clause with {unit})")

                        # Update formula by removing satisfied clauses and literal occurrences
                        new_formula = []
                        for clause in formula:
                            # If clause contains the unit literal, it's satisfied
                            if unit in clause:
                                continue

                            # If clause contains the negation of unit literal, remove it
                            neg_unit = var if unit.startswith('-') else '-' + var
                            if neg_unit in clause:
                                new_clause = clause.copy()
                                new_clause.remove(neg_unit)
                                # If clause becomes empty, we have a conflict
                                if not new_clause:
                                    print(f"  ❌ Derived empty clause after removing {neg_unit}")
                                    return formula, assignment, True
                                new_formula.append(new_clause)
                            else:
                                new_formula.append(clause)

                        formula = new_formula

                        # Check if formula is empty (all clauses satisfied)
                        if not formula:
                            print("  ✅ All clauses satisfied during unit propagation!")
                            return formula, assignment, False

            if propagation_count > 0:
                print(f"  Applied unit propagation for {propagation_count} variables")
            return formula, assignment, False

        def pure_literal_elimination(formula, assignment, level):
            """Eliminate pure literals and return (updated_formula, updated_assignment)."""
            # Find all literal occurrences
            all_literals = set()
            for clause in formula:
                all_literals.update(clause)

            # Check if each variable appears in only one polarity
            for var in variables:
                if var in assignment:
                    continue

                pos_lit = var
                neg_lit = '-' + var

                if pos_lit in all_literals and neg_lit not in all_literals:
                    # Positive literal is pure
                    assignment[var] = (True, level)
                    print(f"  Pure literal elimination: {var} = True (only appears positively)")

                    # Remove clauses containing the pure literal
                    formula = [clause for clause in formula if pos_lit not in clause]

                elif neg_lit in all_literals and pos_lit not in all_literals:
                    # Negative literal is pure
                    assignment[var] = (False, level)
                    print(f"  Pure literal elimination: {var} = False (only appears negatively)")

                    # Remove clauses containing the pure literal
                    formula = [clause for clause in formula if neg_lit not in clause]

            return formula, assignment

        def choose_variable(formula, assignment):
            """Choose the next variable for branching using a simple heuristic."""
            # Count variable occurrences
            var_count = {}
            for clause in formula:
                for lit in clause:
                    var = lit[1:] if lit.startswith('-') else lit
                    if var not in assignment:
                        var_count[var] = var_count.get(var, 0) + 1

            # Choose most frequent unassigned variable
            if var_count:
                return max(var_count.items(), key=lambda x: x[1])[0]
            return None

        def dpll_recursive(formula, assignment, level):
            """Recursive DPLL algorithm with step-by-step output."""
            print(f"\nDecision level {level}")
            print(f"Current assignment: {', '.join([f'{v}={a[0]}' for v, a in sorted(assignment.items())])}")

            if not formula:
                print("  ✅ Formula is empty, all clauses are satisfied!")
                return True, assignment

            # Apply unit propagation
            formula, assignment, conflict = unit_propagation(formula, assignment, level)
            if conflict:
                return False, assignment

            if not formula:
                print("  ✅ Formula is empty after unit propagation, all clauses are satisfied!")
                return True, assignment

            # Apply pure literal elimination
            formula, assignment = pure_literal_elimination(formula, assignment, level)

            if not formula:
                print("  ✅ Formula is empty after pure literal elimination, all clauses are satisfied!")
                return True, assignment

            # Choose variable for branching
            var = choose_variable(formula, assignment)
            if var is None:
                # All variables assigned, check if formula is satisfied
                if not formula:
                    print("  ✅ All variables assigned and formula is satisfied!")
                    return True, assignment
                else:
                    print("  ❌ All variables assigned but formula not satisfied")
                    return False, assignment

            # Try var = True
            print(f"  Branching: trying {var} = True")
            assignment_copy = assignment.copy()
            assignment_copy[var] = (True, level + 1)

            # Update formula for var = True
            new_formula = []
            for clause in formula:
                # If clause contains var, it's satisfied
                if var in clause:
                    continue

                # If clause contains -var, remove it
                neg_var = '-' + var
                if neg_var in clause:
                    new_clause = clause.copy()
                    new_clause.remove(neg_var)
                    # If clause becomes empty, this branch fails
                    if not new_clause:
                        print(f"  ❌ Setting {var} = True leads to empty clause")
                        # Don't need to continue this branch
                    else:
                        new_formula.append(new_clause)
                else:
                    new_formula.append(clause)

            # Recursive call with var = True
            result, final_assignment = dpll_recursive(new_formula, assignment_copy, level + 1)
            if result:
                return True, final_assignment

            # If var = True failed, try var = False
            print(f"  Backtracking: {var} = True failed, trying {var} = False")
            assignment_copy = assignment.copy()
            assignment_copy[var] = (False, level + 1)

            # Update formula for var = False
            new_formula = []
            for clause in formula:
                # If clause contains -var, it's satisfied
                neg_var = '-' + var
                if neg_var in clause:
                    continue

                # If clause contains var, remove it
                if var in clause:
                    new_clause = clause.copy()
                    new_clause.remove(var)
                    # If clause becomes empty, this branch fails
                    if not new_clause:
                        print(f"  ❌ Setting {var} = False leads to empty clause")
                        # Both branches failed
                        print(f"  ❌ Both values for {var} lead to contradiction")
                        return False, assignment
                    new_formula.append(new_clause)
                else:
                    new_formula.append(clause)

            # Recursive call with var = False
            return dpll_recursive(new_formula, assignment_copy, level + 1)

        # Call the DPLL algorithm
        satisfiable, final_assignment = dpll_recursive(formula, assignment, decision_level)

        if satisfiable:
            print("\n✅ Formula is SATISFIABLE")
            print("Satisfying assignment:")
            for var in sorted(variables):
                value = "True" if final_assignment.get(var, (True, 0))[0] else "False"
                print(f"  {var} = {value}")
        else:
            print("\n❌ Formula is UNSATISFIABLE")

        return satisfiable

def generate_formula_from_truth_function(processor, transform_to_dnf=False, transform_to_cnf=False):
    """
    Generate a formula from a truth function represented by the processor's expression.

    Parameters:
        processor (WFFProcessor): The processor object containing the expression and methods for validation.
        transform_to_dnf (bool): Whether to transform the formula to Disjunctive Normal Form (DNF).
        transform_to_cnf (bool): Whether to transform the formula to Conjunctive Normal Form (CNF).
    Returns:
        str: Generated formula based on the truth table results.
    """
    if not processor:
        print("\nNo formula set! Please enter a formula first.")
        return None

    # Get the truth function and initialize a processor for validation.
    processor = WFFProcessor(processor.expression)

    # Validate and generate variables, truth table rows, and results.
    variables, rows, results = processor.silent_validator_and_tree_and_table(processor.expression, processor)
    truth_function = processor.expression

    # If validation fails, return early.
    if variables is False:
        return None
    formula = ""
    # Construct the formula using the truth table.
    if transform_to_dnf:
        if results[truth_function].count(True) != 1:
            formula = "("
        for cnt, truth in enumerate(results[truth_function]):
            if truth:
                # Build the clause
                clause = "("
                for i, variable in enumerate(variables):
                    if rows[cnt][i]:
                        clause += variable
                    else:
                        clause += f"(-{variable})"
                    if i < len(variables) - 1:
                        clause += "&"
                clause += ")"

                # Add to formula and print
                formula += clause + "|"
                print(f"Added DNF clause for row {cnt+1}: {clause} because row {cnt+1} is True in the truth table")

        # Remove the trailing '|' and close the parenthesis.
        if formula.endswith("|"):
            formula = formula[:-1]
        if results[truth_function].count(True) != 1:
            formula += ")"
    elif transform_to_cnf:
        if results[truth_function].count(False) != 1:
            formula = "("
        for cnt, truth in enumerate(results[truth_function]):
            if not truth:
                # Build the clause
                clause = "("
                for i, variable in enumerate(variables):
                    if rows[cnt][i]:
                        clause += f"(-{variable})"
                    else:
                        clause += variable
                    if i < len(variables) - 1:
                        clause += "|"
                clause += ")"

                # Add to formula and print
                formula += clause + "&"
                print(f"Added CNF clause for row {cnt}: {clause} because row {cnt} is False in the truth table")

        # Remove the trailing '&' and close the parenthesis.
        if formula.endswith("&"):
            formula = formula[:-1]
        if results[truth_function].count(False) != 1:
            formula += ")"
    if formula == "()":
        print("The formula is already in the desired form.")
    else:
        print(f"Generated formula: {formula}")
    return formula


class WFFInterface:
    """Interface for interacting with the WFF validator."""

    @staticmethod
    def print_menu():
        """Display the main menu options."""
        print("\n=== Well-Formed Formula (WFF) Validator ===")
        print("1. Enter a new formula")
        print("2. Check if formula is WFF")
        print("3. Display current formula")
        print("4. Display tree representation")
        print("5. Generate truth table")
        print("6. Compare formulas")
        print("7. Truth function as formula")
        print("8. Simplify formula")
        print("9. Display formula to DNF")
        print("10. Display formula to CNF")
        print("11. Display help")
        print("12. Resolution (check unsatisfiability)")
        print("13. DPLL (check satisfiability)")
        print("15. Exit")
        print("=========================================")

    @staticmethod
    def print_help():
        """Display help information about WFF syntax and the tree representation."""
        print("\n=== Help Information ===")
        print("Valid operators:")
        print("  |  : OR")
        print("  &  : AND")
        print("  >  : IMPLIES")
        print("  =  : BICONDITIONAL (IF AND ONLY IF)")
        print("  ^  : XOR (EXCLUSIVE OR)")
        print("  -  : NOT")
        print(" ( )  : Parentheses for grouping")
        print("\nFormula structure:")
        print("- Only single letters are valid (e.g., P, Q, R)")
        print("- Negation: (-P)")
        print("- Binary operations: (P|Q), (P&Q), (P>Q)")
        print("- Complex formulas: ((P|Q)&(-R))")
        print("\nExample: ((((P|Q)&((-P)|Q))>(P&Q))>(-M))")
        print("\nTree Representation:")
        print("- The tree displays the structure of the Well-Formed Formula (WFF)")
        print("- Each node in the tree represents a component of the formula")
        print("- Nodes with labels in [brackets] indicate the current position in the parsing process")
        print("- Nodes with labels in \"double quotes\" represent special nodes:")
        print("  - \"F\" indicates an open placeholder that needs to be filled")
        print("  - \"-\" represents a negation operator waiting to be filled")
        print("  - \"□\" represents a binary operator waiting to be filled")
        print("\nTruth Table:")
        print("- The truth table displays all possible truth values for the formula")
        print("- Each row represents a different combination of truth values for the variables")
        print("- The table will only be generated if there was a tree built from that formula")
        print("===========================")

    def run(self):
        """Run the interactive interface."""
        processor = None

        while True:
            self.print_menu()
            choice = input("Enter your choice (1-15): ").strip()

            if choice == '1':
                current_formula = input("\nEnter your formula: ").strip()
                processor = WFFProcessor(current_formula)
                print(f"Formula set to: {processor.expression}")

            elif choice == '2':
                if not processor:
                    print("\nNo formula set! Please enter a formula first.")
                    continue

                print("\nChecking if formula is WFF...")
                processor.validate_expression()

            elif choice == '3':
                if processor:
                    print(f"\nCurrent formula: {processor.expression}")
                else:
                    print("\nNo formula currently set.")
            elif choice == '4':
                if not processor:
                    print("\nNo formula set! Please enter a formula first.")
                    continue
                processor.get_tree()
            elif choice == '5':
                if not processor:
                    print("\nNo formula set! Please enter a formula first.")
                    continue
                processor.generate_truth_table()
            elif choice == '6':
                """Compare two formulas for equivalence."""
                print("\n=== Compare Formulas ===")
                print("Note that the program will check if the formulas are WFFs and will build the trees.")
                formula1 = input("\nEnter the first formula: ").strip()
                processor = WFFProcessor(formula1)
                a, b, results1 = processor.silent_validator_and_tree_and_table(formula1, processor)
                if a is False:
                    continue
                formula2 = input("\nEnter the second formula: ").strip()
                processor = WFFProcessor(formula2)
                a, b, results2 = processor.silent_validator_and_tree_and_table(formula2, processor)
                if a is False:
                    continue
                values1 = list(results1.values())[0]
                values2 = list(results2.values())[0]
                if values1 == values2:
                    print("The formulas are equivalent.")
                else:
                    print("The formulas are not equivalent.")
                consequence = [i for i, (a, b) in enumerate(zip(values1, values2)) if a == b == True]
                if consequence:
                    print(f"The formulas are consequent.")
                else:
                    print("The formulas are not consequent.")
            elif choice == '7':
                """Generate formula from truth function."""
                text_trap = io.StringIO()
                sys.stdout = text_trap
                formula = generate_formula_from_truth_function(processor, transform_to_dnf=True)
                sys.stdout = sys.__stdout__
                if formula and formula != "()":
                    print(formula)
            elif choice == '8':
                if not processor:
                    print("\nNo formula set! Please enter a formula first.")
                    continue
                print("Simplifying formula ", processor.expression)
                processor.validator_simplificator.simplify_formula()
            elif choice == '9':
                """Transform to DNF."""
                formula = generate_formula_from_truth_function(processor, transform_to_dnf=True)
                if formula:
                    processor.validator_simplificator.simplify_formula()
            elif choice == '10':
                """Transform to CNF."""
                formula = generate_formula_from_truth_function(processor, transform_to_cnf=True)
            elif choice == '11':
                self.print_help()

            elif choice == '12':
                if not processor:
                    print("\nNo formula set! Please enter a formula first.")
                    continue
                start_time = time.time()
                print(f"CNF Formula: {processor.expression}")
                processor.resolution()
                end_time = time.time()
                print("⏱ Runtime: {:.4f} seconds".format(end_time - start_time))

            elif choice == '13':
                if not processor:
                    print("\nNo formula set! Please enter a formula first.")
                    continue
                start_time = time.time()
                print(f"CNF Formula: {processor.expression}")
                processor.dpll()
                end_time = time.time()
                print("⏱ Runtime: {:.4f} seconds".format(end_time - start_time))

            elif choice == '15':
                print("\nThank you for using the WFF Processor!")
                sys.exit(0)

            else:
                print("\nInvalid choice! Please enter a number between 1 and 12.")

            input("\nPress Enter to continue...")


def main():
    """Main entry point of the program."""
    interface = WFFInterface()
    interface.run()


if __name__ == "__main__":
    main()
