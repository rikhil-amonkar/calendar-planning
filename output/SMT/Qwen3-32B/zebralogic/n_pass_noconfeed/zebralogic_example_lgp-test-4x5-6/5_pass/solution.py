import itertools

n = 6  # Number of houses

# Generate all permutations of house positions (1 to n)
house_positions = list(range(1, n + 1))

# Define constraints
def is_valid_plan(perm):
    # Constraint 1: House 1 must be to the left of House 2
    if perm.index(1) >= perm.index(2):
        return False

    # Constraint 2: House 3 must be adjacent to House 4
    idx3 = perm.index(3)
    idx4 = perm.index(4)
    if abs(idx3 - idx4) != 1:
        return False

    # Constraint 3: House 5 must not be adjacent to House 6
    idx5 = perm.index(5)
    idx6 = perm.index(6)
    if abs(idx5 - idx6) == 1:
        return False

    return True

# Generate and filter permutations
valid_plans = []
for perm in itertools.permutations(house_positions):
    if is_valid_plan(perm):
        valid_plans.append(perm)

# Output the result
if valid_plans:
    print("Valid Plan Found:")
    print(valid_plans[0])
else:
    print("No valid plan found under the given constraints.")