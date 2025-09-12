# Example animal list with proper context
animals = ['dog', 'cat', 'rabbit', 'hamster']

# Example usage that won't cause errors
print("List of animals:")
for animal in animals:
    print(f"- {animal}")

# Or if you need to return the list
def get_animals():
    return animals

# Call the function if needed
result = get_animals()
print(result)