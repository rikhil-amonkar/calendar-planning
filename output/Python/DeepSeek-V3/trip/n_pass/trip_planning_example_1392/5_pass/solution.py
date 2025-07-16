visited_days = {}  # Initialize the dictionary

# Example usage within a loop (assuming entries is a list of dictionaries)
entries = [
    {'place': 'Paris', 'days': 3},
    {'place': 'London', 'days': 2},
    # ... other entries
]

for entry in entries:
    visited_days[entry['place'] = visited_days.get(entry['place'], 0) + entry['days']