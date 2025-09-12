import z3

def generate_inclusion_vars(items):
    return [z3.Bool(f'include_{item}') for item in items]

# Example usage
items = ['meeting', 'lunch', 'presentation']
is_included = generate_inclusion_vars(items)