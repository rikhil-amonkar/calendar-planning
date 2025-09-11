# Define the rows of data
rows = [
    [1, "Alice", "Brick", "Tall", "PhD"],
    [2, "Bob", "Wood", "Medium", "Bachelor"],
    [3, "Charlie", "Concrete", "Short", "Master"]
]

# Construct the solution dictionary
solution = {
    "solution": {
        "header": ["House", "Name", "HouseStyle", "Height", "Education"],
        "rows": rows
    }
}

# Optional: Print the solution for verification
print(solution)