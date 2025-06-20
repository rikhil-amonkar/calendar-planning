import random

activities = [
    'Amusement Park', 'Museum', 'Art Gallery', 'Historical Landmark',
    'Aquarium', 'Zoo', 'Botanical Garden', 'Park', 'Beach', 'Shopping District'
]

# Initialize variables for first day
previous_day_activities = []
itinerary = []

# Generate exactly 21 days
for day in range(21):
    if not previous_day_activities:
        # First day: select from all activities
        num_activities = random.choice([2, 3, 4])
        day_activities = random.sample(activities, num_activities)
    else:
        # Subsequent days: exclude previous day's activities
        available = [act for act in activities if act not in previous_day_activities]
        num_activities = random.choice([2, 3, 4])
        day_activities = random.sample(available, num_activities)
    
    # Add to itinerary and set for next day
    itinerary.append(day_activities)
    previous_day_activities = day_activities

# Output each day's activities on separate lines
for day_activities in itinerary:
    print(day_activities)