import itertools
import json

def main():
    # Define cities and their required durations
    cities = ['Split', 'Vilnius', 'Madrid', 'Santorini']
    durations = {
        'Split': 5,
        'Vilnius': 4,
        'Madrid': 6,
        'Santorini': 2
    }
    
    # Define direct flight connections (unordered pairs)
    direct_flights = {
        ('Vilnius', 'Split'),
        ('Split', 'Madrid'),
        ('Madrid', 'Santorini')
    }
    
    # Generate all permutations of the first three cities
    first_three = ['Split', 'Vilnius', 'Madrid']
    valid_orders = []
    
    for perm in itertools.permutations(first_three):
        valid = True
        # Check if consecutive cities have direct flights
        for i in range(len(perm) - 1):
            city_a, city_b = perm[i], perm[i+1]
            if (city_a, city_b) not in direct_flights and (city_b, city_a) not in direct_flights:
                valid = False
                break
        if valid:
            valid_orders.append(list(perm))
    
    # Append Santorini to valid orders if possible
    final_valid_orders = []
    for order in valid_orders:
        last_city = order[-1]
        if (last_city, 'Santorini') in direct_flights or ('Santorini', last_city) in direct_flights:
            new_order = order + ['Santorini']
            final_valid_orders.append(new_order)
    
    # If valid orders exist, compute the itinerary
    if final_valid_orders:
        cities_order = final_valid_orders[0]
        itinerary = []
        current_start_day = 1
        for city in cities_order:
            duration = durations[city]
            end_day = current_start_day + duration - 1
            day_range = f"Day {current_start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
            current_start_day = end_day
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()