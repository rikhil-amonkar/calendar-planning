# Manual schedule
schedule = [
    ("Nob Hill", 9*60, 0),
    ("Union Square", 9*60 + 7, 90),  # Sarah
    ("The Castro", 13*60 + 15, 30),  # Kenneth
    ("Pacific Heights", 13*60 + 45, 15),  # Daniel
    ("North Beach", 14*60, 0),  # Travel to North Beach
    ("North Beach", 14*60 + 8, 0),  # Travel to North Beach
    ("North Beach", 14*60 + 16, 0),  # Travel to North Beach
    ("North Beach", 14*60 + 24, 0),  # Travel to North Beach
    ("North Beach", 14*60 + 32, 0),  # Travel to North Beach
    ("North Beach", 14*60 + 40, 0),  # Travel to North Beach
    ("North Beach", 14*60 + 48, 0),  # Travel to North Beach
    ("North Beach", 14*60 + 56, 0),  # Travel to North Beach
    ("North Beach", 15*60 + 4, 0),  # Travel to North Beach
    ("North Beach", 15*60 + 12, 0),  # Travel to North Beach
    ("North Beach", 15*60 + 20, 0),  # Travel to North Beach
    ("North Beach", 15*60 + 28, 0),  # Travel to North Beach
    ("North Beach", 15*60 + 36, 0),  # Travel to North Beach
    ("North Beach", 15*60 + 44, 0),  # Travel to North Beach
    ("North Beach", 15*60 + 52, 0),  # Travel to North Beach
    ("North Beach", 16*60, 0),  # Travel to North Beach
    ("North Beach", 16*60 + 8, 0),  # Travel to North Beach
    ("North Beach", 16*60 + 16, 0),  # Travel to North Beach
    ("North Beach", 16*60 + 24, 0),  # Travel to North Beach
    ("North Beach", 16*60 + 32, 0),  # Travel to North Beach
    ("North Beach", 16*60 + 40, 0),  # Travel to North Beach
    ("North Beach", 16*60 + 48, 0),  # Travel to North Beach
    ("North Beach", 16*60 + 56, 0),  # Travel to North Beach
    ("North Beach", 17*60 + 4, 0),  # Travel to North Beach
    ("North Beach", 17*60 + 12, 0),  # Travel to North Beach
    ("North Beach", 17*60 + 20, 0),  # Travel to North Beach
    ("North Beach", 17*60 + 28, 0),  # Travel to North Beach
    ("North Beach", 17*60 + 30, 15),  # Meet Thomas
    ("Marina District", 17*60 + 45, 30),  # Meet David
    ("Russian Hill", 18*60 + 30, 120),  # Meet Karen
    ("Embarcadero", 20*60 + 30, 75)  # Meet Mary
]

# Print the schedule
print("SOLUTION:")
for loc, start, duration in schedule:
    print(f"{loc}: Start at {start//60}:{start%60:02d}, Duration {duration} minutes")

# Print the meetings
meetings = [
    ("Sarah", "Union Square", 11*60 + 45, 90),
    ("Kenneth", "The Castro", 13*60 + 15, 30),
    ("Daniel", "Pacific Heights", 13*60 + 45, 15),
    ("Thomas", "North Beach", 19*60 + 15, 15),
    ("David", "Marina District", 20*60, 30),
    ("Karen", "Russian Hill", 20*60 + 30, 120),
    ("Mary", "Embarcadero", 20*60, 75)
]

print("Meetings:")
for friend, loc, start, duration in meetings:
    print(f"{friend} at {loc}: Start at {start//60}:{start%60:02d}, Duration {duration} minutes")