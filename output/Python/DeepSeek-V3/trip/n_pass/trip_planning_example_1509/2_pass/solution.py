import json
from itertools import permutations

def main():
    # Define cities and their required days
    cities = {
        "Paris": 5,
        "Warsaw": 2,
        "Krakow": 2,
        "Tallinn": 2,
        "Riga": 2,
        "Copenhagen": 5,
        "Helsinki": 5,
        "Oslo": 5,
        "Santorini": 2,
        "Lyon": 4
    }

    # Define constraints (city: (start_day, end_day))
    constraints = {
        "Paris": (4, 8),
        "Krakow": (17, 18),
        "Riga": (23, 24),
        "Helsinki": (18, 22),
        "Santorini": (12, 13)
    }

    # Define direct flights
    flights = {
        "Warsaw": ["Riga", "Tallinn", "Copenhagen", "Paris", "Helsinki", "Oslo"],
        "Riga": ["Warsaw", "Paris", "Helsinki", "Copenhagen", "Tallinn", "Oslo"],
        "Tallinn": ["Warsaw", "Oslo", "Helsinki", "Copenhagen", "Paris", "Riga"],
        "Copenhagen": ["Helsinki", "Warsaw", "Lyon", "Oslo", "Santorini", "Krakow", "Riga", "Tallinn", "Paris"],
        "Helsinki": ["Copenhagen", "Warsaw", "Oslo", "Krakow", "Paris", "Riga", "Tallinn"],
        "Oslo": ["Lyon", "Paris", "Copenhagen", "Warsaw", "Riga", "Tallinn", "Helsinki", "Krakow", "Santorini"],
        "Paris": ["Lyon", "Oslo", "Warsaw", "Riga", "Tallinn", "Helsinki", "Krakow", "Copenhagen"],
        "Krakow": ["Helsinki", "Warsaw", "Copenhagen", "Paris", "Oslo"],
        "Santorini": ["Copenhagen", "Oslo"],
        "Lyon": ["Paris", "Oslo", "Copenhagen"]
    }

    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    best_itinerary = None
    best_score = float('inf')

    # We'll try multiple permutations but limit to reasonable number
    for order in permutations(city_names, len(city_names)):
        try:
            # Initialize schedule with 25 empty days
            schedule = [None] * 25
            prev_city = None
            itinerary = []
            
            # First handle constrained cities
            for city in order:
                if city in constraints:
                    start, end = constraints[city]
                    required_days = cities[city]
                    
                    # Check if the constraint fits the required days
                    if end - start + 1 < required_days:
                        continue  # Skip this permutation
                        
                    # Check if the slot is available
                    slot_available = all(schedule[i] is None for i in range(start-1, end))
                    if not slot_available:
                        continue
                        
                    # Place the city in the schedule
                    for i in range(start-1, start-1 + required_days):
                        schedule[i] = city
                        
                    itinerary.append({
                        "day_range": f"Day {start}-{start + required_days - 1}",
                        "place": city
                    })
                    prev_city = city
            
            # Then place unconstrained cities
            for city in order:
                if city not in constraints:
                    required_days = cities[city]
                    placed = False
                    
                    # Try to find a contiguous block of required_days
                    for i in range(25 - required_days + 1):
                        if all(schedule[j] is None for j in range(i, i + required_days)):
                            # Check flight connection if not first city
                            if prev_city and city not in flights.get(prev_city, []):
                                continue
                                
                            # Place the city
                            for j in range(i, i + required_days):
                                schedule[j] = city
                                
                            itinerary.append({
                                "day_range": f"Day {i+1}-{i + required_days}",
                                "place": city
                            })
                            prev_city = city
                            placed = True
                            break
                    
                    if not placed:
                        raise ValueError("Couldn't place city")
            
            # Verify all days are filled and no overlaps
            if None in schedule:
                continue
                
            # Verify all constraints are met
            valid = True
            for city, (start, end) in constraints.items():
                found = False
                for visit in itinerary:
                    if visit["place"] == city:
                        visit_start = int(visit["day_range"].split("-")[0].split(" ")[1])
                        visit_end = int(visit["day_range"].split("-")[1])
                        if visit_start <= start and visit_end >= end:
                            found = True
                            break
                if not found:
                    valid = False
                    break
                    
            if valid:
                # Score based on how compact the schedule is
                score = len(itinerary)  # Fewer segments is better
                if score < best_score:
                    best_score = score
                    best_itinerary = itinerary
                    
        except (ValueError, IndexError):
            continue

    # Output the best itinerary found
    if best_itinerary:
        # Sort itinerary by day range
        best_itinerary.sort(key=lambda x: int(x["day_range"].split("-")[0].split(" ")[1]))
        print(json.dumps({"itinerary": best_itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()