import json

def plan_trip():
    # Define the trip parameters
    total_days = 26
    cities = {
        "Bucharest": {"days": 3, "constraints": []},
        "Venice": {"days": 5, "constraints": ["wedding"]}, 
        "Prague": {"days": 4, "constraints": []},
        "Frankfurt": {"days": 5, "constraints": ["show"]},
        "Zurich": {"days": 5, "constraints": []},
        "Florence": {"days": 5, "constraints": []},
        "Tallinn": {"days": 5, "constraints": ["friends"]}
    }

    # Define the timeline based on constraints
    timeline = []
    current_day = 1

    # Bucharest
    timeline.append({'day_range': f'Day {current_day}-{current_day + cities["Bucharest"]["days"] - 1}', 'place': 'Bucharest'})
    current_day += cities["Bucharest"]["days"]

    # Tallinn
    timeline.append({'day_range': f'Day {current_day}-{current_day + cities["Tallinn"]["days"] - 1}', 'place': 'Tallinn'})
    current_day += cities["Tallinn"]["days"]

    # Meet friends in Tallinn between day 8-12 (covered)
    
    # Frankfurt (Show)
    timeline.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Tallinn', 'to': 'Frankfurt'})
    timeline.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': 'Frankfurt'})
    current_day += 5 # travel included in one day

    # Venice (Wedding)
    timeline.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Frankfurt', 'to': 'Venice'})
    timeline.append({'day_range': f'Day {current_day}-{current_day + cities["Venice"]["days"] - 1}', 'place': 'Venice'})
    current_day += cities["Venice"]["days"]

    # Set aside Days 22-26 in Venice for the wedding
    current_day -= 5  # Go back 5 days for the wedding period
    timeline[-1] = {'day_range': f'Day {current_day + 1}-{current_day + 5}', 'place': 'Venice (Wedding)'}  # Fix wedding

    # Zurich
    timeline.append({'flying': f'Day {current_day + 5}-{current_day + 5}', 'from': 'Venice', 'to': 'Zurich'})
    timeline.append({'day_range': f'Day {current_day + 5}-{current_day + 9}', 'place': 'Zurich'})
    current_day += 5

    # Prague
    timeline.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Zurich', 'to': 'Prague'})
    timeline.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': 'Prague'})
    current_day += 4

    # Florence
    timeline.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Prague', 'to': 'Florence'})
    timeline.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': 'Florence'})
    current_day += 5

    # Verify the final day count
    assert current_day - 1 == total_days, "Total days do not match."

    # Convert plan to JSON
    itinerary_json = json.dumps(timeline, indent=4)
    return itinerary_json

# Run the trip planner
if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)