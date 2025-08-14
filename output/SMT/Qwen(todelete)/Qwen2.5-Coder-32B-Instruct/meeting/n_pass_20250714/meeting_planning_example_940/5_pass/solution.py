# Manual schedule
schedule = [
    ("Jessica", "Russian Hill", 9*60 + 0, 9*60 + 0 + 120),  # 9:00 AM to 1:00 PM
    ("Nancy", "Nob Hill", 9*60 + 45, 9*60 + 45 + 45),      # 9:45 AM to 1:00 PM
    ("John", "North Beach", 9*60 + 45, 9*60 + 45 + 15),     # 9:45 AM to 10:00 AM
    ("Karen", "Chinatown", 16*60 + 45, 16*60 + 45 + 75),   # 4:45 PM to 6:00 PM
    ("Sarah", "Pacific Heights", 17*60 + 30, 17*60 + 30 + 45),  # 5:30 PM to 6:15 PM
    ("Amanda", "The Castro", 20*60 + 0, 20*60 + 0 + 60),  # 8:00 PM to 9:00 PM
    ("Kevin", "Mission District", 20*60 + 45, 20*60 + 45 + 60)  # 8:45 PM to 9:45 PM
]

# Print the schedule
print("SOLUTION:")
for friend, location, start_time, end_time in schedule:
    start_hour, start_minute = divmod(start_time, 60)
    end_hour, end_minute = divmod(end_time, 60)
    print(f"Meet {friend} at {location} from {start_hour:02}:{start_minute:02} to {end_hour:02}:{end_minute:02}")