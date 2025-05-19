import json

def plan_trip():
    # Travel parameters
    total_days = 13
    stay_seville = 2
    stay_stuttgart = 7
    stay_porto = 3
    stay_madrid = 4
    
    # Itinerary setup
    itinerary = []
    
    # Madrid (Day 1-4)
    itinerary.append({'day_range': 'Day 1-4', 'place': 'Madrid'})
    
    # Seville (Day 5-6)
    itinerary.append({'flying': 'Day 5-5', 'from': 'Madrid', 'to': 'Seville'})
    itinerary.append({'day_range': 'Day 5-6', 'place': 'Seville'})
    
    # Porto (Day 7-9)
    itinerary.append({'flying': 'Day 7-7', 'from': 'Seville', 'to': 'Porto'})
    itinerary.append({'day_range': 'Day 7-9', 'place': 'Porto'})
    
    # Stuttgart (Day 10-13)
    itinerary.append({'flying': 'Day 10-10', 'from': 'Porto', 'to': 'Stuttgart'})
    itinerary.append({'day_range': 'Day 10-12', 'place': 'Stuttgart'})
    itinerary.append({'day_range': 'Day 13', 'place': 'Stuttgart'})
    
    # Conference days
    itinerary.append({'conference': 'Day 7 and Day 13', 'city': 'Stuttgart'})

    # Convert to JSON
    trip_plan_json = json.dumps(itinerary, indent=4)
    
    return trip_plan_json

# Run the trip planner and print the output
if __name__ == "__main__":
    planned_trip = plan_trip()
    print(planned_trip)