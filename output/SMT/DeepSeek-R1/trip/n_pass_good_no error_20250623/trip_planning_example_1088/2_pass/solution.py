import random

def generate_itinerary():
    activities = [
        'Amusement Park', 'Museum', 'Art Gallery', 'Historical Landmark', 
        'Aquarium', 'Zoo', 'Botanical Garden', 'Park', 'Beach', 'Shopping District'
    ]
    itinerary = []
    
    # Generate the first day
    num_activities = random.choice([2, 3, 4])
    day_activities = random.sample(activities, num_activities)
    itinerary.append(day_activities)
    
    # Generate the remaining 20 days
    for _ in range(1, 21):
        # Activities available: those not used in the previous day
        available_activities = [act for act in activities if act not in itinerary[-1]]
        num_activities = random.choice([2, 3, 4])
        day_activities = random.sample(available_activities, num_activities)
        itinerary.append(day_activities)
    
    return itinerary

# Generate and print the itinerary
itinerary = generate_itinerary()
for day_activities in itinerary:
    print(day_activities)