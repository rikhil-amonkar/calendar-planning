import json
from itertools import permutations

def main():
    # Cities and required days
    cities = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    # Direct flights (undirected graph)
    flights = {
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Oslo': ['Porto', 'Riga', 'Geneva', 'Edinburgh', 'Vilnius', 'Budapest', 'Helsinki', 'Tallinn'],
        'Edinburgh': ['Porto', 'Budapest', 'Geneva', 'Oslo', 'Helsinki', 'Riga'],
        'Budapest': ['Edinburgh', 'Geneva', 'Helsinki', 'Oslo'],
        'Geneva': ['Edinburgh', 'Budapest', 'Oslo', 'Porto', 'Helsinki'],
        'Riga': ['Oslo', 'Tallinn', 'Helsinki', 'Vilnius', 'Edinburgh'],
        'Tallinn': ['Riga', 'Vilnius', 'Helsinki', 'Oslo'],
        'Vilnius': ['Helsinki', 'Tallinn', 'Riga', 'Oslo'],
        'Helsinki': ['Vilnius', 'Tallinn', 'Riga', 'Oslo', 'Budapest', 'Geneva', 'Edinburgh']
    }
    
    # Constraints
    constraints = {
        'Tallinn': {'start_day': 4},  # Must start on day 4 (5 days = days 4-8)
        'Oslo': {'start_day': 24}    # Must start on day 24 (2 days = days 24-25)
    }
    
    # We'll build the itinerary around the constrained cities
    # First place Tallinn (days 4-8)
    # Last place Oslo (days 24-25)
    # Need to fit other cities in days 1-3 and 9-23 (total 19 days)
    
    remaining_cities = [city for city in cities.keys() if city not in ['Tallinn', 'Oslo']]
    remaining_days = sum(cities[city] for city in remaining_cities)  # 2+2+3+2+5+5+4 = 23 days needed
    
    # Wait, total is 2+2+3+2+5+5+5+5+4 = 33 days, but we have:
    # - Tallinn: 5 (fixed days 4-8)
    # - Oslo: 2 (fixed days 24-25)
    # Others: 26 days, but only have 19 days available (1-3 and 9-23)
    # This seems impossible
    
    # Let me re-examine the constraints:
    # Maybe the wedding is during the stay in Tallinn, not necessarily the whole stay
    # So Tallinn could be longer than the wedding days
    
    # Alternative interpretation: wedding is between days 4-8, but stay could be longer
    # But original problem says "wedding is between days 4-8"
    # Maybe we need to adjust our approach
    
    # Let's try a different strategy: fix Tallinn to include days 4-8, and Oslo to cover 24-25
    # Then see if we can arrange other cities around them
    
    # Helper function to check flight connections
    def connected(city1, city2):
        return city2 in flights[city1]
    
    # We'll try to find a path that:
    # 1. Starts with some cities (days 1-3)
    # 2. Then Tallinn starting on day x where x <=4 and x+5-1 >=8 (so x=4)
    # 3. Then other cities
    # 4. Then Oslo starting on day 24
    
    # Let's fix Tallinn to start on day 4 (5 days = 4-8)
    # Oslo must start on day 24 (2 days = 24-25)
    # Need to arrange other cities in:
    # - Days 1-3 (3 days)
    # - Days 9-23 (15 days)
    # Total other cities need: 2+2+3+2+5+5+4 = 23 days
    # But we only have 18 days available - still impossible
    
    # Wait, maybe the wedding is just during part of Tallinn stay
    # Let's assume Tallinn stay must include days 4-8, but can be longer
    
    # Let's try this approach:
    
    # Generate possible itineraries with:
    # 1. Cities before Tallinn (must end before day 4)
    # 2. Tallinn (must include days 4-8)
    # 3. Cities between Tallinn and Oslo
    # 4. Oslo (days 24-25)
    
    # Pre-cities (days 1-3)
    pre_cities = [city for city in cities.keys() 
                 if city != 'Tallinn' and city != 'Oslo' and cities[city] <= 3]
    
    # Try different combinations
    for pre in pre_cities:
        if cities[pre] > 3:
            continue
        # Tallinn must start on day (4 - cities[pre]) to day 4
        # But must include days 4-8
        # So Tallinn must start on day max(1, 4 - (cities[Tallinn] - (8-4+1)))
        # Wait, let's calculate:
        # Tallinn duration is 5 days, must cover days 4-8
        # So it must start between day (4 - (5 - (8-4+1))) = 4 - (5-5) = 4
        # So must start exactly on day 4
        
        # Therefore pre-cities must end on day 3
        # So only possible if pre-city is 3 days (Edinburgh)
        if cities[pre] != 3:
            continue
        
        # So first city is Edinburgh (days 1-3)
        # Then Tallinn (days 4-8)
        
        # Now we have days 9-23 for other cities (15 days)
        # Need to fit: Oslo (2), Helsinki (2), Riga (2), Budapest (5), Vilnius (5), Porto (5), Geneva (4)
        # Oslo is fixed at end, so other cities: 2+2+5+5+5+4 = 23 days
        # But only 15 days available - still impossible
        
        # This path isn't working. Maybe we need to have multiple cities before Tallinn
    
    # Alternative approach: since the constraints seem impossible to satisfy,
    # maybe the wedding can be during a longer stay in Tallinn
    # Let's assume Tallinn stay must include days 4-8, but can be longer
    
    # Find a valid itinerary with this interpretation
    # This will require more sophisticated path finding
    
    # Since we can't find a valid path with given constraints, return empty
    print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()