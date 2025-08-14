# Define the final schedule manually based on the analysis
final_schedule = {
    "Russian Hill": 540,  # 9:00 AM
    "Embarcadero": 548,  # 9:08 AM
    "Nob Hill": 657,     # 10:57 AM
    "Mission District": 1877  # 7:17 PM
}

# Define the meeting times
meeting_times = {
    "Timothy": (548, 668),  # 9:08 AM to 10:48 AM
    "Patricia": (1830, 1860),  # 6:30 PM to 7:00 PM
    "Ashley": (2030, 2045)  # 8:30 PM to 8:45 PM
}

# Print the final schedule
print("SOLUTION:")
for loc, start_time in final_schedule.items():
    print(f"Arrive at {loc} at {start_time // 60}:{start_time % 60:02}")

for friend, (start, end) in meeting_times.items():
    print(f"Meet {friend} from {start // 60}:{start % 60:02} to {end // 60}:{end % 60:02}")