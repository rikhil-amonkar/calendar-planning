# Define the time points in minutes since 9:00 AM
start_time = 0  # 9:00 AM
laura_start = 180  # 12:15 PM
laura_end = 465  # 7:45 PM
anthony_start = 195  # 12:30 PM
anthony_end = 285  # 2:45 PM

# Define the travel times in minutes
travel_times = {
    ('castro', 'mission'): 7,
    ('castro', 'financial'): 20,
    ('mission', 'castro'): 7,
    ('mission', 'financial'): 17,
    ('financial', 'castro'): 23,
    ('financial', 'mission'): 17
}

# Manually set the meeting times
meet_laura_start = 180  # Start at 12:15 PM
meet_laura_end = 255  # End at 1:15 PM
meet_anthony_start = 282  # Start at 1:42 PM
meet_anthony_end = 312  # End at 2:12 PM

# Convert the meeting times to HH:MM format
def convert_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

meet_laura_start_time = convert_to_time(meet_laura_start)
meet_laura_end_time = convert_to_time(meet_laura_end)
meet_anthony_start_time = convert_to_time(meet_anthony_start)
meet_anthony_end_time = convert_to_time(meet_anthony_end)

print("SOLUTION:")
print(f"Meet Laura from {meet_laura_start_time} to {meet_laura_end_time}")
print(f"Meet Anthony from {meet_anthony_start_time} to {meet_anthony_end_time}")