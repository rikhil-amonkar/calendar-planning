# Manually constructed feasible schedule
solution = {
    "Rebecca": (420, 465),
    "Nancy": (570, 660),
    "Jessica": (675, 720)
}

# Print the solution
print("SOLUTION:")
for friend, (start, end) in solution.items():
    start_time = start - 540  # Convert to minutes after 9:00 AM
    end_time = end - 540      # Convert to minutes after 9:00 AM
    print(f"Meet {friend} from {start_time} to {end_time} minutes after 9:00 AM")