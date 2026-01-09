import json

def main():
    # Define cities and their required days
    cities = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    
    # Define direct flight connections
    connections = {
        'Lisbon': ['Paris', 'Seville', 'Prague', 'Valencia', 'Nice', 'Oslo', 'Lyon'],
        'Paris': ['Lisbon', 'Oslo', 'Valencia', 'Nice', 'Lyon', 'Tallinn', 'Prague', 'Seville'],
        'Lyon': ['Nice', 'Prague', 'Paris', 'Valencia', 'Oslo'],
        'Nice': ['Lyon', 'Paris', 'Mykonos', 'Oslo', 'Lisbon'],
        'Oslo': ['Tallinn', 'Paris', 'Prague', 'Nice', 'Lyon', 'Lisbon'],
        'Seville': ['Lisbon', 'Paris', 'Valencia'],
        'Tallinn': ['Oslo', 'Paris', 'Prague'],
        'Mykonos': ['Nice'],
        'Prague': ['Lyon', 'Lisbon', 'Oslo', 'Paris', 'Valencia', 'Tallinn'],
        'Valencia': ['Paris', 'Lisbon', 'Lyon', 'Seville', 'Prague']
    }
    
    # Start with Lisbon (good connectivity)
    itinerary = []
    current_day = 1
    visited = set()
    
    # Start in Lisbon
    lisbon_days = cities['Lisbon']
    itinerary.append({
        "day_range": f"Day {current_day}-{current_day + lisbon_days - 1}",
        "place": "Lisbon"
    })
    visited.add('Lisbon')
    current_day += lisbon_days
    
    # Function to find next valid city
    def find_next_city(current_city, current_day, visited):
        # Prioritize cities with special constraints first
        special_cities = [
            ('Seville', 5, 9),    # Must be between day 5-9
            ('Valencia', 3, 4),   # Must be between day 3-4  
            ('Oslo', 13, 15),     # Must be between day 13-15
            ('Mykonos', 21, 25)   # Must be between day 21-25
        ]
        
        # Check special cities first
        for city, min_day, max_day in special_cities:
            if (city not in visited and 
                city in connections.get(current_city, []) and
                current_day <= max_day and
                current_day + cities[city] - 1 <= 25):
                # Check if this fits the special constraint window
                end_day = current_day + cities[city] - 1
                if end_day >= min_day and current_day <= max_day:
                    return city
        
        # Then try other connected cities
        for next_city in connections.get(current_city, []):
            if (next_city not in visited and 
                current_day + cities[next_city] - 1 <= 25):
                return next_city
        
        return None
    
    # Build itinerary step by step
    current_city = 'Lisbon'
    
    while len(visited) < len(cities) and current_day <= 25:
        next_city = find_next_city(current_city, current_day, visited)
        
        if next_city is None:
            # If no direct connection, try to find any unvisited city
            for city in cities:
                if city not in visited and current_day + cities[city] - 1 <= 25:
                    # Find a path through connected cities
                    for intermediate in connections.get(current_city, []):
                        if intermediate in connections.get(city, []):
                            next_city = city
                            break
                    if next_city:
                        break
        
        if next_city is None:
            break
            
        # Add travel day
        travel_day = current_day
        current_day += 1  # Travel day
        
        # Add the city visit
        city_days = cities[next_city]
        end_day = current_day + city_days - 1
        
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": next_city
        })
        
        visited.add(next_city)
        current_city = next_city
        current_day = end_day + 1
    
    # Check if we visited all cities
    if len(visited) == len(cities):
        # Generate travel days information
        travel_days = []
        for i in range(1, len(itinerary)):
            prev_city = itinerary[i-1]['place']
            current_city = itinerary[i]['place']
            prev_end_day = int(itinerary[i-1]['day_range'].split('-')[-1])
            travel_day = prev_end_day + 1
            travel_days.append(f"Travel from {prev_city} to {current_city} on Day {travel_day}")
        
        print(json.dumps({
            "itinerary": itinerary,
            "travel_days": travel_days
        }, indent=2))
    else:
        print(json.dumps({
            "error": f"Could not visit all cities. Visited: {len(visited)}/{len(cities)}",
            "visited": list(visited),
            "current_day": current_day
        }))

if __name__ == "__main__":
    main()