import json
from itertools import permutations
from collections import defaultdict

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Istanbul': 4,
        'Vienna': 4,
        'Riga': 2,
        'Brussels': 2,
        'Madrid': 4,
        'Vilnius': 4,
        'Venice': 5,
        'Geneva': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    
    # Special constraints with day ranges
    constraints = {
        'Brussels': {'wedding': (26, 27)},
        'Vilnius': {'friends': (20, 23)},
        'Venice': {'workshop': (7, 11)},
        'Geneva': {'relatives': (1, 4)}
    }
    
    # Direct flight connections (undirected)
    flights = {
        'Munich': ['Vienna', 'Madrid', 'Venice', 'Reykjavik', 'Istanbul', 'Brussels', 'Geneva'],
        'Vienna': ['Munich', 'Vilnius', 'Istanbul', 'Venice', 'Riga', 'Brussels', 'Geneva', 'Madrid', 'Reykjavik'],
        'Istanbul': ['Brussels', 'Geneva', 'Vienna', 'Riga', 'Venice', 'Munich', 'Madrid', 'Vilnius'],
        'Brussels': ['Istanbul', 'Venice', 'Riga', 'Reykjavik', 'Vilnius', 'Vienna', 'Madrid', 'Geneva', 'Munich'],
        'Madrid': ['Munich', 'Venice', 'Vienna', 'Brussels', 'Istanbul', 'Geneva'],
        'Vilnius': ['Vienna', 'Istanbul', 'Brussels', 'Munich', 'Riga'],
        'Venice': ['Brussels', 'Munich', 'Madrid', 'Vienna', 'Istanbul'],
        'Geneva': ['Istanbul', 'Vienna', 'Brussels', 'Madrid', 'Munich'],
        'Riga': ['Brussels', 'Istanbul', 'Vienna', 'Munich', 'Vilnius'],
        'Reykjavik': ['Munich', 'Vienna', 'Brussels', 'Madrid']
    }
    
    # Total days
    total_days = 27
    
    # Try different starting points (must start in Geneva due to day 1-4 constraint)
    start_city = 'Geneva'
    
    # We'll use backtracking to find a valid itinerary
    def backtrack(current_city, remaining_cities, current_day, itinerary, city_days_spent):
        # Base case: all cities visited and we've used exactly 27 days
        if not remaining_cities and current_day == total_days + 1:
            return itinerary
        
        # If we've exceeded total days
        if current_day > total_days:
            return None
        
        # Check if we need to be in a specific city due to constraints
        required_city = None
        for city, constr in constraints.items():
            for event, (start, end) in constr.items():
                if start <= current_day <= end:
                    required_city = city
                    break
            if required_city:
                break
        
        # If we're required to be in a city but we're not there
        if required_city and current_city != required_city:
            # Check if we can fly there
            if required_city in flights[current_city]:
                # Fly to required city
                new_itinerary = itinerary + [(current_day, f"Fly from {current_city} to {required_city}")]
                result = backtrack(required_city, remaining_cities, current_day + 1, new_itinerary, city_days_spent.copy())
                if result:
                    return result
            return None
        
        # Try staying in current city if we haven't completed its days
        if city_days_spent[current_city] < cities[current_city]:
            # Check if staying violates any constraints
            can_stay = True
            for city, constr in constraints.items():
                if city != current_city:
                    for event, (start, end) in constr.items():
                        if start <= current_day <= end:
                            can_stay = False
                            break
                if not can_stay:
                    break
            
            if can_stay:
                new_city_days = city_days_spent.copy()
                new_city_days[current_city] += 1
                new_itinerary = itinerary + [(current_day, f"Stay in {current_city}")]
                
                # Check if we've completed this city
                new_remaining = remaining_cities.copy()
                if new_city_days[current_city] == cities[current_city] and current_city in new_remaining:
                    new_remaining.remove(current_city)
                
                result = backtrack(current_city, new_remaining, current_day + 1, new_itinerary, new_city_days)
                if result:
                    return result
        
        # Try flying to other cities
        for next_city in flights[current_city]:
            # Only consider cities we haven't completed or need more days in
            if next_city in remaining_cities or city_days_spent[next_city] < cities[next_city]:
                # Check if flying violates constraints
                can_fly = True
                for city, constr in constraints.items():
                    for event, (start, end) in constr.items():
                        if start <= current_day <= end and city != next_city:
                            can_fly = False
                            break
                    if not can_fly:
                        break
                
                if can_fly:
                    new_itinerary = itinerary + [(current_day, f"Fly from {current_city} to {next_city}")]
                    result = backtrack(next_city, remaining_cities, current_day + 1, new_itinerary, city_days_spent.copy())
                    if result:
                        return result
        
        return None
    
    # Initial setup
    initial_city_days = {city: 0 for city in cities}
    initial_remaining = set(cities.keys())
    initial_remaining.remove(start_city)  # We're starting in Geneva
    
    # We need to spend first days in Geneva (1-4)
    initial_itinerary = []
    for day in range(1, 5):
        initial_itinerary.append((day, f"Stay in {start_city}"))
    initial_city_days[start_city] = 4
    
    # Start backtracking from day 5
    result = backtrack(start_city, initial_remaining, 5, initial_itinerary, initial_city_days)
    
    if not result:
        return {"error": "No valid itinerary found"}
    
    # Process the result into the required format
    itinerary_dict = {}
    current_place = None
    start_day = 1
    
    for day, action in result:
        if "Stay in" in action:
            place = action.replace("Stay in ", "")
            if place != current_place:
                if current_place:
                    itinerary_dict[f"Day {start_day}-{day-1}"] = current_place
                current_place = place
                start_day = day
        elif "Fly from" in action:
            # On flight days, we're transitioning
            parts = action.replace("Fly from ", "").split(" to ")
            from_city, to_city = parts[0], parts[1]
            # End the previous city stay
            if current_place:
                itinerary_dict[f"Day {start_day}-{day}"] = current_place
            current_place = to_city
            start_day = day + 1
    
    # Add the last stay
    if current_place:
        itinerary_dict[f"Day {start_day}-27"] = current_place
    
    # Convert to list format
    itinerary_list = [{"day_range": day_range, "place": place} for day_range, place in itinerary_dict.items()]
    
    return {"itinerary": itinerary_list}

def main():
    result = solve_itinerary()
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()