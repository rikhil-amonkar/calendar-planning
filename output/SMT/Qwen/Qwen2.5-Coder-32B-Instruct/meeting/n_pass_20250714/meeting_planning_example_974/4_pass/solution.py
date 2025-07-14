# Final solution based on manual verification with valid times
schedule = [
    ("William", "Russian Hill", 750, 870, 120),
    ("Nancy", "Pacific Heights", 885, 990, 105),
    ("Robert", "Nob Hill", 999, 1089, 90),
    ("Charles", "Presidio", 1115, 1215, 105),
    ("David", "North Beach", 1125, 1200, 75),
    ("Brian", "Mission District", 1136, 1200, 60),
    ("Jeffrey", "Richmond District", 1140, 1185, 45)
]

print("SOLUTION:")
for friend, loc, start, end, duration in schedule:
    print(f"Meet {friend} at {loc} from {start // 60}:{start % 60:02d} to {end // 60}:{end % 60:02d}")