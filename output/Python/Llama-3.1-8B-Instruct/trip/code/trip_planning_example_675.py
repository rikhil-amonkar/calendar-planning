import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Dubrovnik': 4,
            'Split': 3,
            'Milan': 3,
            'Porto': 4,
            'Krakow': 2,
            'Munich': 5
        }
        self.flights = {
            ('Munich', 'Porto'): 1,
            ('Split', 'Milan'): 1,
            ('Milan', 'Porto'): 1,
            ('Munich', 'Krakow'): 1,
            ('Munich', 'Milan'): 1,
            ('Dubrovnik', 'Munich'): 1,
            ('Krakow', 'Split'): 1,
            ('Krakow', 'Milan'): 1,
            ('Munich', 'Split'): 1
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

        # Add wedding and show constraints
        for i, item in enumerate(optimal_itinerary):
            if 'Milan' in item['place'] and days_in_city == 3 and 11 <= days_left + days_in_city <= 13:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'
            if 'Munich' in item['place'] and days_in_city == 5 and 4 <= days_left + days_in_city <= 8:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        # Add meeting constraint
        for i, item in enumerate(optimal_itinerary):
            if 'Krakow' in item['place'] and days_in_city == 2 and 8 <= days_left + days_in_city <= 9:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
        days = 16
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())