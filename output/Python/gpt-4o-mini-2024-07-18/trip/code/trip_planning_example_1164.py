import json

def create_itinerary():
    itinerary = []
    
    # Define days allocated to each city and constraints
    days = {
        "Reykjavik": 2,
        "Stockholm": 2,
        "Porto": 5,
        "Nice": 3,
        "Venice": 4,
        "Vienna": 3,
        "Split": 3,
        "Copenhagen": 2
    }
    
    # Define travel order based on constraints
    travel_plan = [
        ("Reykjavik", 1, 2),
        ("Stockholm", 3, 4),
        ("Copenhagen", 10, 11),  # Before Vienna
        ("Vienna", 11, 13),
        ("Porto", 13, 17),
        ("Nice", 5, 7),
        ("Venice", 8, 11),
        ("Split", 10, 12)
    ]
    
    current_day = 1
    
    # Add Reykjavik to itinerary
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Reykjavik'})
    current_day += 2  # Move to next available day
    
    # Adding Stockholm
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Stockholm'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Stockholm'})
    current_day += 2  # Move to next day
    
    # Adding Nice
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Stockholm', 'to': 'Nice'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': 'Nice'})
    current_day += 3  # Move to next day
    
    # Adding Venice
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Nice', 'to': 'Venice'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': 'Venice'})
    current_day += 4  # Move to next day
    
    # Adding Split
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Venice', 'to': 'Split'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': 'Split'})
    current_day += 3  # Move to next day
    
    # Adding Vienna
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Vienna'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': 'Vienna'})
    current_day += 3  # Move to next day
    
    # Adding Copenhagen
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Copenhagen'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Copenhagen'})
    current_day += 2  # Move to next day
    
    # Finally, adding Porto for the wedding
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Copenhagen', 'to': 'Porto'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': 'Porto'})
    
    # Convert itinerary to JSON format
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    print(create_itinerary())