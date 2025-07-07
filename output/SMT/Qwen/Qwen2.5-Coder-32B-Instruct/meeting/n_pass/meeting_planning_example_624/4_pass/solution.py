# Define the schedule manually with correct times
schedule = [
    ('Karen', 'The Castro', 13, 88),
    ('Deborah', 'Alamo Square', 96, 201),
    ('Laura', 'Fisherman\'s Wharf', 221, 281),
    ('Elizabeth', 'Chinatown', 293, 368),
    ('Jason', 'North Beach', 374, 464),
    ('Steven', 'Russian Hill', 468, 588)
]

# Function to convert minutes to a readable time format
def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Print the schedule with correct time format
print("SOLUTION:")
for name, location, start, end in schedule:
    start_time = minutes_to_time(start)
    end_time = minutes_to_time(end)
    print(f"Meet {name} at {start_time} for {end - start} minutes")