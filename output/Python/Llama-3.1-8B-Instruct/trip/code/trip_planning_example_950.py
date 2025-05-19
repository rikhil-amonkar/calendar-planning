import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Mykonos': 3,
            'Riga': 3,
            'Munich': 4,
            'Bucharest': 4,
            'Rome': 4,
            'Nice': 3,
            'Krakow': 2
        }
        self.flights = {
            ('Nice', 'Riga'): 1,
            ('Bucharest', 'Munich'): 1,
            ('Mykonos', 'Munich'): 1,
            ('Riga', 'Bucharest'): 1,
            ('Rome', 'Nice'): 1,
            ('Rome', 'Munich'): 1,
            ('Mykonos', 'Nice'): 1,
            ('Rome', 'Mykonos'): 1,
            ('Munich', 'Krakow'): 1,
            ('Rome', 'Bucharest'): 1,
            ('Nice', 'Munich'): 1,
            ('Riga', 'Munich'): 1,
            ('Rome', 'Riga'): 1
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

        # Add wedding constraint
        for i, item in enumerate(optimal_itinerary):
            if 'Mykonos' in item['place'] and days_in_city == 3 and 4 <= days_left + days_in_city <= 6:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        # Add conference constraints
        for i, item in enumerate(optimal_itinerary):
            if 'Rome' in item['place'] and days_in_city == 4 and 1 <= days_left + days_in_city <= 4:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'
            if 'Rome' in item['place'] and days_in_city == 4 and 4 <= days_left + days_in_city <= 7:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        # Add annual show constraint
        for i, item in enumerate(optimal_itinerary):
            if 'Krakow' in item['place'] and days_in_city == 2 and 16 <= days_left + days_in_city <= 17:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Mykonos', 'Riga', 'Munich', 'Bucharest', 'Rome', 'Nice', 'Krakow']
        days = 17
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())