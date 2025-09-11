# Example initialization of name_map and hair_color_perm
name_map = {
    "Eric": 3,
    "Alice": 1,
    "Bob": 2
}

hair_color_perm = ["brown", "blonde", "red"]

# Ensure "blonde" is in the list and "Eric" is a key in the dictionary
if "blonde" in hair_color_perm and "Eric" in name_map:
    # Calculate the index of "blonde" in hair_color_perm
    blonde_index = hair_color_perm.index("blonde")
    
    # Check if the condition holds
    result = name_map[blonde_index] - 1 == name_map["Eric"]
    print(result)
else:
    print("Either 'blonde' is not in hair_color_perm or 'Eric' is not in name_map.")