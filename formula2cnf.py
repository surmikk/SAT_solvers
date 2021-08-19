import sys
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('infile', nargs='?', type=argparse.FileType('r', encoding='UTF-8'), default=sys.stdin)
parser.add_argument('outfile', nargs='?', type=argparse.FileType('w', encoding='UTF-8'), default=sys.stdout)
parser.add_argument("--implications_only", default=False, type=bool, help="Use only left-to-right implications")


class Node:
    """Node in a binary tree"""
    def __init__(self, operation, variable, left, right):
        self.operation = operation
        self.var = variable
        self.left = left
        self.right = right


def get_tokens(input):
    for line in input:
        for token in line.translate({ord('('): ' ', ord(')'): ' '}).split():
            yield token


def get_variable_node(variable_string, variables, negation=False):
    if not (variable_string.isalnum() and variable_string[0].isalpha()):
        raise Exception("Wrong name of variable '" + variable_string + "'")

    if variable_string in variables:
        var_id = variables[variable_string]
    else:
        var_id = len(variables) + 1
        variables[variable_string] = var_id
    if negation:
        var_id = -var_id
    return Node(None, var_id, None, None)


def load_formula(tokens, variables):
    token = next(tokens)

    if token == "not":
        result = get_variable_node(next(tokens), variables, negation=True)
    elif token in ["and", "or"]:
        new_var_id = len(variables) + 1          # variable id of given node
        variables[str(new_var_id)] = new_var_id  # auxiliary item for correct dictionary length
        result = Node(
            operation=token,
            variable=new_var_id,
            left=load_formula(tokens, variables),
            right=load_formula(tokens, variables)
        )
    else:
        result = get_variable_node(token, variables)
    return result


def extract_clauses(node, implications_only, clauses_list):
    if node.operation is None:
        return

    if node.operation == 'or':
        if node.left.var != -node.right.var:                # avoiding 'True' clause
            clauses_list.append([-node.var, node.left.var, node.right.var])
    else:
        clauses_list.append([-node.var, node.left.var])
        clauses_list.append([-node.var, node.right.var])

    if not implications_only:
        if node.operation == 'or':
            clauses_list.append([-node.left.var, node.var])
            clauses_list.append([-node.right.var, node.var])
        else:
            if node.left.var != -node.right.var:            # avoiding 'True' clause
                clauses_list.append([-node.left.var, -node.right.var, node.var])

    extract_clauses(node.left, implications_only, clauses_list)
    extract_clauses(node.right, implications_only, clauses_list)


def load_smtlib(input, implications_only=False):
    variables = dict()
    tokens = get_tokens(input)
    root = load_formula(tokens, variables)
    clauses = []
    extract_clauses(root, implications_only, clauses)
    return clauses, variables


def tseitin_encoding(input, output, implications_only=False):
    clauses, variables = load_smtlib(input, implications_only)
    original_variables_mapping = {}
    auxiliary_variables = []
    for k, v in variables.items():
        if k.isdigit():
            auxiliary_variables.append(int(k))
        else:
            original_variables_mapping[k] = v

    print('c', file=output)
    print('c Mapping from original variables to numbers:', file=output)
    print('c', original_variables_mapping, file=output)
    print('c List of auxiliary variables:', file=output)
    print('c', auxiliary_variables, file=output)
    print('c Variable corresponding to root node: 1', file=output)
    print('c', file=output)
    print('p cnf', len(variables), len(clauses), file=output)

    for clause in clauses:
        print(*clause, 0, file=output)


if __name__ == "__main__":
    args = parser.parse_args()
    tseitin_encoding(args.infile, args.outfile, args.implications_only)