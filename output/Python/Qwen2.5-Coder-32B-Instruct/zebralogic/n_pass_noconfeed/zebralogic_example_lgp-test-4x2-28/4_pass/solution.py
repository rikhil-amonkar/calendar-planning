# Example initialization of name_map and hair_color_perm
name_map = {
    "Eric": 3,
    "Alice": 1,
    "Bob": 2
}

hair_color_perm = ["brown", "blonde", "red"]

# Dictionary mapping names to their hair colors
hair_color_map = {
    "Eric": "brown",
    "Alice": "blonde",
    "Bob": "red"
}

# Ensure "blonde" is in the list and there is a person with blonde hair
if "blonde" in hair_color_perm and any(hair_color_map[name] == "blonde" for name in hair_color_map):
    # Find the person with blonde hair
    blonde_person = next(name for name, color in hair_color_map.items() if color == "blonde")
    
    # Get the index of "blonde" in hair_color_perm
    blonde_index = hair_color_perm.index("blonde")
    
    # Check if the condition holds
    result = name_map[blonde_person] - 1 == name_map["Eric"]
    print(result)
else:
    print("Either 'blonde' is not in hair_color_perm or there is no person with blonde hair.")