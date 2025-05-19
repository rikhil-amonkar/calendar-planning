import json
from itertools import permutations

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Paris': 5,
        'Warsaw': 2,
        'Krakow': 2,
        'Tallinn': 2,
        'Riga': 2,
        'Copenhagen': 5,
        'Helsinki': 5,
        'Oslo': 5,
        'Santorini': 2,
        'Lyon': 4
    }
    
    # Define constraints
    constraints = {
        'Paris': {'meet_friends': (4, 8)},
        'Krakow': {'workshop': (17, 18)},
        'Riga': {'wedding': (23, 24)},
        'Helsinki': {'meet_friend': (18, 22)},
        'Santorini': {'visit_relatives': (12, 13)}
    }
    
    # Define direct flights (undirected graph)
    direct_flights = {
        'Warsaw': ['Riga', 'Tallinn', 'Copenhagen', 'Paris', 'Helsinki', 'Oslo', 'Krakow'],
        'Riga': ['Warsaw', 'Paris', 'Oslo', 'Helsinki', 'Tallinn', 'Copenhagen'],
        'Tallinn': ['Warsaw', 'Oslo', 'Helsinki', 'Copenhagen', 'Riga'],
        'Copenhagen': ['Helsinki', 'Warsaw', 'Lyon', 'Oslo', 'Krakow', 'Riga', 'Tallinn', 'Paris', 'Santorini'],
        'Helsinki': ['Copenhagen', 'Oslo', 'Warsaw', 'Paris', 'Krakow', 'Riga', 'Tallinn'],
        'Oslo': ['Lyon', 'Paris', 'Copenhagen', 'Warsaw', 'Riga', 'Tallinn', 'Helsinki', 'Krakow', 'Santorini'],
        'Krakow': ['Helsinki', 'Warsaw', 'Copenhagen', 'Paris', 'Oslo'],
        'Paris': ['Lyon', 'Oslo', 'Copenhagen', 'Warsaw', 'Riga', 'Tallinn', 'Helsinki', 'Krakow'],
        'Santorini': ['Copenhagen', 'Oslo'],
        'Lyon': ['Paris', 'Copenhagen', 'Oslo']
    }
    
    # Generate all possible city orders that visit all cities
    city_names = list(cities.keys())
    
    # We'll use a heuristic approach since full permutation is too expensive
    # Start with Paris since it has early constraints
    start_city = 'Paris'
    remaining_cities = city_names.copy()
    remaining_cities.remove(start_city)
    
    # Try permutations of remaining cities
    best_itinerary = None
    best_score = float('inf')
    
    # Limit permutations to make it computationally feasible
    for _ in range(1000):  # Adjust based on needed precision vs performance
        import random
        random.shuffle(remaining_cities)
        candidate_order = [start_city] + remaining_cities
        
        # Check if order is feasible based on flights
        feasible = True
        for i in range(len(candidate_order)-1):
            if candidate_order[i+1] not in direct_flights[candidate_order[i]]:
                feasible = False
                break
        if not feasible:
            continue
        
        # Try to schedule this order
        itinerary = []
        current_day = 1
        prev_city = None
        
        for city in candidate_order:
            if prev_city is not None:
                # Add flight day
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 1  # Assume flights take 1 day
            
            # Add stay
            stay_duration = cities[city]
            end_day = current_day + stay_duration - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            
            # Check constraints
            if city in constraints:
                for constraint, (start, end) in constraints[city].items():
                    if not (current_day <= start and end <= end_day):
                        feasible = False
                        break
                if not feasible:
                    break
            
            prev_city = city
            current_day = end_day + 1
        
        if feasible and current_day - 1 <= 25:
            # Calculate a score (lower is better)
            score = current_day - 1  # Total days used
            if score < best_score:
                best_score = score
                best_itinerary = itinerary.copy()
    
    if best_itinerary is None:
        return []  # No feasible itinerary found
    
    return best_itinerary

def main():
    itinerary = find_itinerary()
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()