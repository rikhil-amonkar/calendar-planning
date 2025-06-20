import random

def generate_itinerary():
    activities = [
        'Amusement Park', 'Museum', 'Art Gallery', 'Historical Landmark', 
        'Aquarium', 'Zoo', 'Botanical Garden', 'Park', 'Beach', 'Shopping District'
    ]
    itinerary = []
    
    # Generate first day with 2-4 random activities
    num_activities = random.choice([2, 3, 4])
    day_activities = random.sample(activities, num_activities)
    itinerary.append(day_activities)
    
    # Generate 20 additional days
    for _ in range(20):
        # Exclude previous day's activities
        available_activities = [act for act in activities if act not in itinerary[-1]]
        num_activities = random.choice([2, 3, 4])
        day_activities = random.sample(available_activities, num_activities)
        itinerary.append(day_activities)
    
    return itinerary

# Generate and verify itinerary
itinerary = generate_itinerary()
assert len(itinerary) == 21, f"Expected 21 days, got {len(itinerary)}"

# Print daily activities
for day_activities in itinerary:
    print(day_activities)