# Example friends list
friends = [
    {'name': 'Alice', 'location': 'Office', 'earliest_start': 9, 'required': 2},
    {'name': 'Bob', 'location': 'Home', 'earliest_start': 10, 'required': 1},
    {'name': 'Charlie', 'location': 'Library', 'earliest_start': 11, 'required': 3}
]

itinerary = []

for friend in friends:
    earliest_start = friend['earliest_start']
    required = friend['required']
    itinerary.append((
        friend['name'],
        friend['location'],
        earliest_start,
        earliest_start + required
    ))

print(itinerary)