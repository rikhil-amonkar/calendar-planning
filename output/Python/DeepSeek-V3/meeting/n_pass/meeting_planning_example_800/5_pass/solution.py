def time_to_minutes(time_str):
    """Convert time string (HH:MM) to minutes since midnight"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Sample friends data with their available time slots
friends = [
    {'name': 'Alice', 'start': '09:00', 'end': '11:00', 'duration': 120},
    {'name': 'Bob', 'start': '10:00', 'end': '12:00', 'duration': 60},
    {'name': 'Charlie', 'start': '14:00', 'end': '15:30', 'duration': 90}
]

# Sort friends by available time window (end - start) and then by duration
prioritized_friends = sorted(friends, key=lambda x: (time_to_minutes(x['end']) - time_to_minutes(x['start']), x['duration']))

print("Prioritized friends:")
for friend in prioritized_friends:
    print(f"{friend['name']}: Available from {friend['start']} to {friend['end']} (Duration: {friend['duration']} minutes)")