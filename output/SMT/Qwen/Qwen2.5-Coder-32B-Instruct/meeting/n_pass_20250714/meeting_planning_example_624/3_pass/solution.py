# Define the schedule manually
schedule = [
    ('Karen', 'The Castro', 13, 88),
    ('Deborah', 'Alamo Square', 96, 201),
    ('Laura', 'Fisherman\'s Wharf', 221, 281),
    ('Elizabeth', 'Chinatown', 293, 368),
    ('Jason', 'North Beach', 374, 464),
    ('Steven', 'Russian Hill', 468, 588)
]

# Print the schedule
print("SOLUTION:")
for name, location, start, end in schedule:
    print(f"Meet {name} at {start} for {end - start} minutes")