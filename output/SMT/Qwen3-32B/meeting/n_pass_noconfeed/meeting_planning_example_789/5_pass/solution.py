# Define conditions and values
cond0 = True  # Example boolean condition
val0 = 10     # Value if cond0 is True
cond1 = False # Another boolean condition
val1 = 20     # Value if cond1 is True
cond2 = True  # Another boolean condition
val2 = 30     # Value if cond2 is True

# Nested ternary expression
result = val0 if cond0 else (val1 if cond1 else (val2 if cond2 else 0))
print(result)  # Output: 10 (since cond0 is True)