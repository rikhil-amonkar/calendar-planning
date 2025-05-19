import json

class TripPlanner:
    def __init__(self):
        self.cities = {
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
        self.flights = {
            ('Porto', 'Oslo'): 1,
            ('Edinburgh', 'Budapest'): 1,
            ('Edinburgh', 'Geneva'): 1,
            ('Riga', 'Tallinn'): 1,
            ('Edinburgh', 'Porto'): 1,
            ('Vilnius', 'Helsinki'): 1,
            ('Tallinn', 'Vilnius'): 1,
            ('Riga', 'Oslo'): 1,
            ('Geneva', 'Oslo'): 1,
            ('Edinburgh', 'Oslo'): 1,
            ('Edinburgh', 'Helsinki'): 1,
            ('Vilnius', 'Oslo'): 1,
            ('Riga', 'Helsinki'): 1,
            ('Budapest', 'Geneva'): 1,
            ('Helsinki', 'Budapest'): 1,
            ('Helsinki', 'Oslo'): 1,
            ('Edinburgh', 'Riga'): 1,
            ('Tallinn', 'Helsinki'): 1,
            ('Geneva', 'Porto'): 1,
            ('Budapest', 'Oslo'): 1,
            ('Helsinki', 'Geneva'): 1,
            ('Riga', 'Vilnius'): 1,
            ('Tallinn', 'Oslo'): 1
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

        # Add meeting constraint
        for i, item in enumerate(optimal_itinerary):
            if 'Oslo' in item['place'] and days_in_city == 2 and 24 <= days_left + days_in_city <= 25:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
        days = 25
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())