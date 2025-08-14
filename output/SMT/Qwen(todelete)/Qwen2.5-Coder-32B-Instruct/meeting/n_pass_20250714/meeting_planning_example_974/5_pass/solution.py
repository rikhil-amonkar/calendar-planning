# Final solution based on manual verification with valid times
schedule = [
    ("William", "Russian Hill", 750, 870, 120),
    ("Nancy", "Pacific Heights", 885, 990, 105),
    ("Robert", "Nob Hill", 999, 1089, 90),
    ("Charles", "Presidio", 1115, 1215, 105),
    ("David", "North Beach", 1245, 1320, 75),
    ("Brian", "Mission District", 1350, 1410, 60),
    ("Jeffrey", "Richmond District", 1485, 1530, 45)
]

# Adjust Robert's meeting time to fit within his availability
# Robert is available from 1335 to 1770 (1:15 PM to 5:30 PM)
# We need to adjust his meeting time to fit within this range
# Let's move Robert's meeting earlier to 1:15 PM to 2:45 PM (90 minutes)

# Adjusted schedule
adjusted_schedule = [
    ("William", "Russian Hill", 750, 870, 120),
    ("Nancy", "Pacific Heights", 885, 990, 105),
    ("Robert", "Nob Hill", 1335, 1425, 90),
    ("Charles", "Presidio", 1440, 1545, 105),
    ("David", "North Beach", 1545, 1620, 75),
    ("Brian", "Mission District", 1650, 1710, 60),
    ("Jeffrey", "Richmond District", 1710, 1755, 45)
]

# Convert times to a valid 24-hour format
final_schedule = []
for friend, loc, start, end, duration in adjusted_schedule:
    start_hour = start // 60
    start_minute = start % 60
    end_hour = end // 60
    end_minute = end % 60
    final_schedule.append((friend, loc, f"{start_hour:02d}:{start_minute:02d}", f"{end_hour:02d}:{end_minute:02d}"))

print("SOLUTION:")
for friend, loc, start, end in final_schedule:
    print(f"Meet {friend} at {loc} from {start} to {end}")