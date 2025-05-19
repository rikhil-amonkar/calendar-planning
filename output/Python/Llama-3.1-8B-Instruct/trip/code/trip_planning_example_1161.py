import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Mykonos': 4,
            'Krakow': 5,
            'Vilnius': 2,
            'Helsinki': 2,
            'Dubrovnik': 3,
            'Oslo': 2,
            'Madrid': 5,
            'Paris': 2
        }
        self.flights = {
            ('Oslo', 'Krakow'): 1,
            ('Oslo', 'Paris'): 1,
            ('Paris', 'Madrid'): 1,
            ('Helsinki', 'Vilnius'): 1,
            ('Oslo', 'Madrid'): 1,
            ('Oslo', 'Helsinki'): 1,
            ('Helsinki', 'Krakow'): 1,
            ('Dubrovnik', 'Helsinki'): 1,
            ('Dubrovnik', 'Madrid'): 1,
            ('Oslo', 'Dubrovnik'): 1,
            ('Krakow', 'Paris'): 1,
            ('Madrid', 'Mykonos'): 1,
            ('Oslo', 'Vilnius'): 1,
            ('Krakow', 'Vilnius'): 1,
            ('Helsinki', 'Paris'): 1,
            ('Vilnius', 'Paris'): 1,
            ('Helsinki', 'Madrid'): 1
        }

    def generate_itinerary(self, days, constraints):
        # Sort cities by duration in descending order
        sorted_cities = sorted(constraints, key=lambda x: self.cities[x], reverse=True)

        # Initialize the optimal itinerary
        optimal_itinerary = []

        # Iterate over cities to find the optimal itinerary
        for i, city in enumerate(sorted_cities):
            days_in_city = self.cities[city]
            if i == 0:
                days_left = days - days_in_city
                optimal_itinerary.append({'day_range': f'Day 1-{days_in_city}', 'place': city})
            else:
                if (sorted_cities[i-1], city) in self.flights:
                    days_left -= 1
                    optimal_itinerary.append({'flying': f'Day {days_left+1}-{days_left+1}', 'from': sorted_cities[i-1], 'to': city})
                days_left -= days_in_city
                optimal_itinerary.append({'day_range': f'Day {days_left+1}-{days_left+days_in_city}', 'place': city})

        # Add annual show constraint
        for i, item in enumerate(optimal_itinerary):
            if 'Dubrovnik' in item['place'] and days_in_city == 3 and 2 <= days_left + days_in_city <= 4:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        # Add relatives constraint
        for i, item in enumerate(optimal_itinerary):
            if 'Mykonos' in item['place'] and days_in_city == 4 and 15 <= days_left + days_in_city <= 18:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        # Add meeting constraint
        for i, item in enumerate(optimal_itinerary):
            if 'Oslo' in item['place'] and days_in_city == 2 and 1 <= days_left + days_in_city <= 2:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Mykonos', 'Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 'Oslo', 'Madrid', 'Paris']
        days = 18
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())