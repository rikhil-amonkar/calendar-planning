# Define a valid, task-specific plan for calculating average temperature from a dataset

plan = [
    "Step 1: Load the dataset containing daily temperature readings (e.g., from a CSV file).",
    "Step 2: Parse and clean the data (remove missing values, convert strings to floats).",
    "Step 3: Sum all valid temperature readings.",
    "Step 4: Count the number of valid temperature entries.",
    "Step 5: Calculate the average temperature by dividing the sum by the count.",
    "Step 6: Print or return the average temperature.",
    "Step 7: Handle edge cases (e.g., empty dataset, non-numeric values)."
]

# Print the plan
for step in plan:
    print(step)