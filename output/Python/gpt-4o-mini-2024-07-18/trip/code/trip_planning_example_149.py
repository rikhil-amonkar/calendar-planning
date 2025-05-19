import json

def plan_trip():
    # Trip parameters
    total_days = 10
    london_days = 3
    santorini_days = 6
    istanbul_days = 3
    conference_days = [5, 10]
    
    # Create a list to hold the itinerary
    itinerary = []
    
    # Day 1-3: Stay in London
    itinerary.append({'day_range': 'Day 1-3', 'place': 'London'})
    
    # Day 4: Travel from London to Santorini
    itinerary.append({'flying': 'Day 4-4', 'from': 'London', 'to': 'Santorini'})
    
    # Day 4-6: Stay in Santorini (Day 5 is a conference)
    itinerary.append({'day_range': 'Day 4-6', 'place': 'Santorini'})
    
    # Day 7-8: Stay in Istanbul
    itinerary.append({'flying': 'Day 7-7', 'from': 'Santorini', 'to': 'Istanbul'})
    itinerary.append({'day_range': 'Day 7-8', 'place': 'Istanbul'})
    
    # Day 9: Fly back to Santorini for conference on Day 10
    itinerary.append({'flying': 'Day 9-9', 'from': 'Istanbul', 'to': 'Santorini'})
    
    # Day 9-10: Stay in Santorini (Day 10 is another conference)
    itinerary.append({'day_range': 'Day 9-10', 'place': 'Santorini'})
    
    # Convert itinerary to JSON format
    itinerary_json = json.dumps(itinerary, indent=4)
    
    return itinerary_json

# Execute the trip planner and print the result
if __name__ == "__main__":
    print(plan_trip())