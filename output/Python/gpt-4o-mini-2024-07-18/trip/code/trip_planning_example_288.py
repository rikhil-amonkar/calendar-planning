import json

def plan_trip():
    # Define the trip parameters
    trip_info = {
        "total_days": 15,
        "cities": {
            "Stuttgart": {"stay": 5, "constraints": ["workshop", "day_11_to_15"]},
            "Manchester": {"stay": 7, "constraints": ["wedding", "day_1_to_7"]},
            "Madrid": {"stay": 4, "constraints": []},
            "Vienna": {"stay": 2, "constraints": []}
        },
        "direct_flights": [
            ("Vienna", "Stuttgart"),
            ("Manchester", "Vienna"),
            ("Madrid", "Vienna"),
            ("Manchester", "Stuttgart"),
            ("Manchester", "Madrid")
        ]
    }

    # Initialize the itinerary list
    itinerary = []
    current_day = 1

    # 1. Attend the wedding in Manchester (Day 1 to 7)
    itinerary.append({'day_range': 'Day 1-7', 'place': 'Manchester'})
    current_day += 7

    # 2. Fly to Stuttgart (Day 8 to 12)
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Manchester', 'to': 'Stuttgart'})
    itinerary.append({'day_range': f'Day {current_day+1}-{current_day+5}', 'place': 'Stuttgart'})
    current_day += 5

    # 3. Fly to Vienna (Day 13 to 14)
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Stuttgart', 'to': 'Vienna'})
    itinerary.append({'day_range': f'Day {current_day+1}-{current_day+2}', 'place': 'Vienna'})
    current_day += 2

    # 4. Fly to Madrid (Day 15 to 15)
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vienna', 'to': 'Madrid'})
    itinerary.append({'day_range': f'Day {current_day+1}-{current_day+4}', 'place': 'Madrid'})

    # Organizing final itinerary output for JSON
    output = json.dumps(itinerary, indent=4)
    return output

# Execute the trip planning function and print the result
print(plan_trip())