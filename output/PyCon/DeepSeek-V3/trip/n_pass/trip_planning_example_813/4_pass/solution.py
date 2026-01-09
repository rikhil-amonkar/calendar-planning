import json
from itertools import permutations

def main():
    # Cities and their required days
    cities = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }
    
    # Direct flight connections (bidirectional)
    flights = {
        'Frankfurt': ['Dublin', 'London', 'Vilnius', 'Stuttgart'],
        'Dublin': ['Frankfurt', 'London', 'Seville', 'Santorini'],
        'London': ['Frankfurt', 'Dublin', 'Santorini', 'Stuttgart'],
        'Vilnius': ['Frankfurt'],
        'Stuttgart': ['Frankfurt', 'London'],
        'Seville': ['Dublin'],
        'Santorini': ['London', 'Dublin']
    }
    
    # Total days
    total_days = 17
    
    # Special constraints - must visit on at least one of these days
    london_meet_days = [9, 10]  # Must be in London on day 9 OR 10
    stuttgart_relatives_days = [7, 8, 9]  # Must be in Stuttgart on day 7, 8, OR 9
    
    # Generate all possible city permutations
    city_names = list(cities.keys())
    valid_itineraries = []
    
    for city_order in permutations(city_names):
        # Check flight connections between consecutive cities
        valid_connections = True
        for i in range(len(city_order) - 1):
            city1, city2 = city_order[i], city_order[i+1]
            # Check if cities are connected (bidirectional)
            if city2 not in flights.get(city1, []) or city1 not in flights.get(city2, []):
                valid_connections = False
                break
        if not valid_connections:
            continue
            
        # Try different start days for the itinerary
        for start_day in range(1, total_days + 1):
            current_day = start_day
            itinerary = []
            valid_schedule = True
            
            for i, city in enumerate(city_order):
                # Check if we exceed total days
                if current_day + cities[city] - 1 > total_days:
                    valid_schedule = False
                    break
                
                # Add this city stay
                end_day = current_day + cities[city] - 1
                itinerary.append({
                    "city": city,
                    "start_day": current_day,
                    "end_day": end_day
                })
                
                # Move to next city (add travel day)
                if i < len(city_order) - 1:
                    current_day = end_day + 1  # Travel day
                
            if not valid_schedule:
                continue
                
            # Check London constraint - must be in London on at least one of days 9 or 10
            london_satisfied = False
            for stay in itinerary:
                if stay["city"] == "London":
                    # Check if the stay covers at least one of the required days
                    for day in london_meet_days:
                        if stay["start_day"] <= day <= stay["end_day"]:
                            london_satisfied = True
                            break
                    if london_satisfied:
                        break
            if not london_satisfied:
                continue
                
            # Check Stuttgart constraint - must be in Stuttgart on at least one of days 7, 8, or 9
            stuttgart_satisfied = False
            for stay in itinerary:
                if stay["city"] == "Stuttgart":
                    # Check if the stay covers at least one of the required days
                    for day in stuttgart_relatives_days:
                        if stay["start_day"] <= day <= stay["end_day"]:
                            stuttgart_satisfied = True
                            break
                    if stuttgart_satisfied:
                        break
            if not stuttgart_satisfied:
                continue
                
            # If we get here, we have a valid itinerary
            formatted_itinerary = []
            for stay in itinerary:
                if stay["start_day"] == stay["end_day"]:
                    day_range = f"Day {stay['start_day']}"
                else:
                    day_range = f"Day {stay['start_day']}-{stay['end_day']}"
                formatted_itinerary.append({
                    "day_range": day_range,
                    "place": stay["city"]
                })
            
            valid_itineraries.append(formatted_itinerary)
            # Stop after finding first valid itinerary to save computation
            break
    
    if valid_itineraries:
        # Return the first valid itinerary
        result = {"itinerary": valid_itineraries[0]}
        print(json.dumps(result, indent=2))
    else:
        result = {"itinerary": [], "error": "No valid itinerary found that satisfies all constraints"}
        print(json.dumps(result))

if __name__ == "__main__":
    main()