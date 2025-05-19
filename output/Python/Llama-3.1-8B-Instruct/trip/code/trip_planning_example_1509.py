import json

class TripPlanner:
    def __init__(self):
        self.cities = {
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
        self.flights = {
            ('Warsaw', 'Riga'): 1,
            ('Warsaw', 'Tallinn'): 1,
            ('Copenhagen', 'Helsinki'): 1,
            ('Lyon', 'Paris'): 1,
            ('Copenhagen', 'Warsaw'): 1,
            ('Lyon', 'Oslo'): 1,
            ('Paris', 'Oslo'): 1,
            ('Paris', 'Riga'): 1,
            ('Krakow', 'Helsinki'): 1,
            ('Paris', 'Tallinn'): 1,
            ('Oslo', 'Riga'): 1,
            ('Krakow', 'Warsaw'): 1,
            ('Paris', 'Helsinki'): 1,
            ('Copenhagen', 'Santorini'): 1,
            ('Helsinki', 'Warsaw'): 1,
            ('Helsinki', 'Riga'): 1,
            ('Copenhagen', 'Krakow'): 1,
            ('Copenhagen', 'Riga'): 1,
            ('Paris', 'Krakow'): 1,
            ('Copenhagen', 'Oslo'): 1,
            ('Oslo', 'Tallinn'): 1,
            ('Oslo', 'Helsinki'): 1,
            ('Copenhagen', 'Tallinn'): 1,
            ('Oslo', 'Krakow'): 1,
            ('Riga', 'Tallinn'): 1,
            ('Helsinki', 'Tallinn'): 1,
            ('Paris', 'Copenhagen'): 1,
            ('Paris', 'Warsaw'): 1,
            ('Santorini', 'Oslo'): 1,
            ('Oslo', 'Warsaw'): 1
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

        # Add wedding and workshop constraints
        for i, item in enumerate(optimal_itinerary):
            if 'Riga' in item['place'] and days_in_city == 2 and 23 <= days_left + days_in_city <= 24:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'
            if 'Krakow' in item['place'] and days_in_city == 2 and 17 <= days_left + days_in_city <= 18:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'
            if 'Helsinki' in item['place'] and days_in_city == 5 and 18 <= days_left + days_in_city <= 22:
                optimal_itinerary[i]['day_range'] = f'Day {days_left+1}-{days}'

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
        days = 25
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())