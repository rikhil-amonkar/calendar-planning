# Example definition of name_perm
name_perm = ["Alice", "Bob", "Carol", "David", "Eric"]

# Example definition of house_dict
house_dict = {
    "Alice": {"house": 1},
    "Bob": {"house": 2},
    "Carol": {"house": 3},
    "David": {"house": 4},
    "Eric": {"house": 5}
}

# Comparison
if house_dict[name_perm.index("Carol")]["house"] > house_dict[name_perm.index("Eric")]["house"]:
    print("Carol's house number is greater than Eric's.")
else:
    print("Carol's house number is not greater than Eric's.")