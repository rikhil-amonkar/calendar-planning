import json

# Initialize the lists for names and vacations
names = [None] * 6
vacations = [None] * 6

# Apply constraints
# Constraint 4 & 7
vacations[2] = 'cultural'
names[2] = 'Peter'

# Constraint 3
names[1] = 'Eric'

# Constraint 9
vacations[3] = 'city'

# Constraint 8
# We need to find Bob's house later

# Constraint 5
# Bob is directly left of Arnold
# We'll determine this after other placements

# Constraint 6
# Camping is not in the first house
# We'll determine this after other placements

# Constraint 1
# Cultural is left of Beach
# Peter is in house 3, so Beach must be in house 4, 5, or 6

# Deduction steps:
# Bob must be in house 5, Arnold in house 6
# Alice must be in house 1 (cannot be in house 2)
# Carol must be in house 4 (city break is in house 4)
# Remaining are Eric and Arnold
# Beach must be in house 6, Mountain in house 1

# Assign based on deductions
names[0] = 'Alice'
vacations[0] = 'mountain'

names[3] = 'Carol'

names[4] = 'Bob'
vacations[4] = 'cruise'

names[5] = 'Arnold'
vacations[5] = 'beach'

# Eric is already placed in house 2
# The only remaining vacation for Eric is camping
vacations[1] = 'camping'

# Construct the solution in the required JSON format
solution = {
    "solution": {
        "header": ["House", "Name", "Vacation"],
        "rows": [
            ["1", names[0], vacations[0]],
            ["2", names[1], vacations[1]],
            ["3", names[2], vacations[2]],
            ["4", names[3], vacations[3]],
            ["5", names[4], vacations[4]],
            ["6", names[5], vacations[5]]
        ]
    }
}

# Output the solution as JSON
print(json.dumps(solution, indent=2))