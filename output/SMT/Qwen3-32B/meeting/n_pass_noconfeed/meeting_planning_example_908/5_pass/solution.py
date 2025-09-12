friends = [
    {'location': 1, 'duration': 30, 'available_start': 540, 'available_end': 600},
    {'location': 2, 'duration': 45, 'available_start': 570, 'available_end': 630},
    # ... (rest of the friends as provided)
]

# Example: Check if all friends have enough available time for their duration
for friend in friends:
    available_time = friend['available_end'] - friend['available_start']
    if available_time >= friend['duration']:
        print(f"Friend {friend['location']} has enough time.")
    else:
        print(f"Friend {friend['location']} does NOT have enough time.")