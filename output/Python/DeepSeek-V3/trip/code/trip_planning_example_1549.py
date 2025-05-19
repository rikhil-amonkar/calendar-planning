import json
from itertools import permutations

def main():
    # Input parameters
    cities = {
        'Prague': 5,
        'Tallinn': 3,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 5,
        'Milan': 3,
        'Lisbon': 5,
        'Santorini': 5,
        'Riga': 4,
        'Stockholm': 2
    }
    
    constraints = [
        {'city': 'Tallinn', 'day_range': (18, 20)},
        {'city': 'Milan', 'day_range': (24, 26)},
        {'city': 'Riga', 'day_range': (5, 8)}
    ]
    
    direct_flights = {
        'Riga': ['Prague', 'Milan', 'Tallinn', 'Stockholm', 'Warsaw'],
        'Stockholm': ['Milan', 'Lisbon', 'Santorini', 'Warsaw', 'Prague', 'Tallinn', 'Riga'],
        'Milan': ['Stockholm', 'Riga', 'Naples', 'Porto', 'Prague', 'Lisbon', 'Santorini', 'Warsaw'],
        'Lisbon': ['Stockholm', 'Warsaw', 'Naples', 'Porto', 'Prague', 'Riga', 'Milan'],
        'Naples': ['Warsaw', 'Milan', 'Lisbon', 'Santorini'],
        'Warsaw': ['Naples', 'Lisbon', 'Stockholm', 'Riga', 'Porto', 'Tallinn', 'Milan', 'Prague'],
        'Porto': ['Lisbon', 'Milan', 'Warsaw'],
        'Prague': ['Riga', 'Tallinn', 'Stockholm', 'Lisbon', 'Milan', 'Warsaw'],
        'Tallinn': ['Riga', 'Prague', 'Stockholm', 'Warsaw'],
        'Santorini': ['Stockholm', 'Milan', 'Naples']
    }
    
    # Generate all possible city permutations
    city_names = list(cities.keys())
    possible_sequences = permutations(city_names)
    
    def is_valid_sequence(sequence):
        # Check if all constraints are met
        day = 1
        itinerary = []
        
        for i, city in enumerate(sequence):
            duration = cities[city]
            end_day = day + duration - 1
            
            # Check constraints for this city
            for constraint in constraints:
                if constraint['city'] == city:
                    if not (constraint['day_range'][0] <= day <= constraint['day_range'][1] or 
                           constraint['day_range'][0] <= end_day <= constraint['day_range'][1] or 
                           (day <= constraint['day_range'][0] and end_day >= constraint['day_range'][1])):
                        return False
            
            itinerary.append((city, day, end_day))
            day = end_day + 1
            
            # Check flight connection to next city
            if i < len(sequence) - 1:
                next_city = sequence[i + 1]
                if next_city not in direct_flights[city]:
                    return False
        
        # Check total days
        total_days = sum(cities[city] for city in sequence)
        if total_days != 28:
            return False
        
        return True
    
    # Find a valid sequence
    valid_sequence = None
    for seq in possible_sequences:
        if is_valid_sequence(seq):
            valid_sequence = seq
            break
    
    if not valid_sequence:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Generate itinerary
    itinerary = []
    day = 1
    for i, city in enumerate(valid_sequence):
        duration = cities[city]
        end_day = day + duration - 1
        itinerary.append({'day_range': f'Day {day}-{end_day}', 'place': city})
        
        if i < len(valid_sequence) - 1:
            next_city = valid_sequence[i + 1]
            itinerary.append({'flying': f'Day {end_day + 1}-{end_day + 1}', 'from': city, 'to': next_city})
            day = end_day + 2  # +1 for flying day, +1 for next day
    
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()