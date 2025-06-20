import random

def generate_itinerary():
    activities = [
        'Amusement Park', 'Museum', 'Art Gallery', 'Historical Landmark', 
        'Aquarium', 'Zoo', 'Botanical Garden', 'Park', 'Beach', 'Shopping District'
    ]
    itinerary = []
    previous_day_activities = []  # Empty for first day
    
    # Generate all 21 days
    for day in range(21):
        if not previous_day_activities:
            # First day: use all activities
            available_activities = activities
        else:
            # Exclude activities from previous day
            available_activities = [act for act in activities if act not in previous_day_activities]
        
        # Choose 2-4 activities
        num_activities = random.choice([2, 3, 4])
        day_activities = random.sample(available_activities, num_activities)
        
        itinerary.append(day_activities)
        previous_day_activities = day_activities  # Set for next day
    
    # Final validation
    if len(itinerary) != 21:
        raise RuntimeError(f"Generated {len(itinerary)} days instead of 21")
    return itinerary

# Generate and print itinerary
itinerary = generate_itinerary()
for day_activities in itinerary:
    print(day_activities)