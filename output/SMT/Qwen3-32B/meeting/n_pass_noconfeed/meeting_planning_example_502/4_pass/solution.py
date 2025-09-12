def generate_inclusion_vars(items):
    return [Bool(f'include_{item}') for item in items]

# Example usage
items = ['meeting', 'lunch', 'presentation']
is_included = generate_inclusion_vars(items)