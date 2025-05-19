import json
from itertools import chain, combinations

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Brussels': 4,
            'Bucharest': 3,
            'Stuttgart': 4,
            'Mykonos': 2,
            'Madrid': 4,
            'Helsinki': 5,
            'Split': 3,
            'London': 5
        }
        self.flights = {
            ('Helsinki', 'London'): 1,
            ('Split', 'Madrid'): 1,
            ('Helsinki', 'Madrid'): 1,
            ('London', 'Madrid'): 1,
            ('Brussels', 'London'): 1,
            ('Bucharest', 'London'): 1,
            ('Brussels', 'Bucharest'): 1,
            ('Bucharest', 'Madrid'): 1,
            ('Split', 'Helsinki'): 1,
            ('Mykonos', 'Madrid'): 1,
            ('Stuttgart', 'London'): 1,
            ('Helsinki', 'Brussels'): 1,
            ('Brussels', 'Madrid'): 1,
            ('Split', 'London'): 1,
            ('Stuttgart', 'Split'): 1,
            ('London', 'Mykonos'): 1
        }

    def powerset(self, iterable):
        s = list(iterable)
        return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

    def generate_itinerary(self, days, constraints):
        # Generate all possible combinations of cities
        possible_combinations = list(self.powerset(constraints))

        # Filter combinations that do not meet the day constraint
        valid_combinations = []
        for combination in possible_combinations:
            days_in_combination = sum(self.cities[city] for city in combination)
            if days_in_combination <= days:
                valid_combinations.append(combination)

        # Initialize the optimal itinerary
        optimal_itinerary = []

        # Iterate over valid combinations to find the optimal itinerary
        for combination in valid_combinations:
            days_in_combination = sum(self.cities[city] for city in combination)
            days_left = days - days_in_combination
            itinerary = [{'day_range': f'Day {days_left+1}-{days_left+days_in_combination}', 'place': city} for city in combination]
            for i in range(len(combination) - 1):
                if (combination[i], combination[i+1]) in self.flights:
                    days_left += 1
                    itinerary.append({'flying': f'Day {days_left}-{days_left}', 'from': combination[i], 'to': combination[i+1]})
            optimal_itinerary = max([optimal_itinerary, itinerary], key=lambda x: len(x))

        return optimal_itinerary

    def plan_trip(self):
        constraints = ['Helsinki', 'Stuttgart', 'Mykonos', 'Madrid', 'Helsinki', 'Split', 'London']
        days = 21
        itinerary = self.generate_itinerary(days, constraints)
        return json.dumps(itinerary, indent=4)

if __name__ == '__main__':
    trip_planner = TripPlanner()
    print(trip_planner.plan_trip())