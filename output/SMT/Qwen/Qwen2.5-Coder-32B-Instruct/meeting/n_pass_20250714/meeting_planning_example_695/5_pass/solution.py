# Define the manual schedule
schedule = [
    {"name": "Nancy", "location": "Presidio", "start": 11.75, "end": 12.25},
    {"name": "Karen", "location": "The Castro", "start": 12.5, "end": 13.25},
    {"name": "Matthew", "location": "Russian Hill", "start": 13.45, "end": 15.6833},
    {"name": "Carol", "location": "Union Square", "start": 15.0, "end": 17.0},
    {"name": "Paul", "location": "Nob Hill", "start": 17.0833, "end": 18.0833}
]

# Print the schedule
print("SOLUTION:")
for meeting in schedule:
    print(f"Meet {meeting['name']} at {meeting['location']} from {meeting['start']} to {meeting['end']}")