import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Tallinn': {'duration': 2, 'fixed_range': None, 'visited': False},
            'Bucharest': {'duration': 4, 'fixed_range': (1, 4), 'visited': False},
            'Seville': {'duration': 5, 'fixed_range': (8, 12), 'visited': False},
            'Stockholm': {'duration': 5, 'fixed_range': None, 'visited': False},
            'Munich': {'duration': 5, 'fixed_range': (4, 8), 'visited': False},
            'Milan': {'duration': 2, 'fixed_range': None, 'visited': False},
        }
        self.direct_flights = [
            ('Milan', 'Stockholm'), ('Munich', 'Stockholm'), ('Bucharest', 'Munich'), 
            ('Munich', 'Seville'), ('Stockholm', 'Tallinn'), ('Munich', 'Milan'), 
            ('Munich', 'Tallinn'), ('Seville', 'Milan')
        ]
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Plan fixed ranges first
        for city, info in self.cities.items():
            if info['fixed_range']:
                self.plan_fixed_range(city, info['fixed_range'], info['duration'])

        # Plan remaining cities
        while any(not info['visited'] for info in self.cities.values()):
            for city, info in self.cities.items():
                if not info['visited']:
                    self.plan_city(city, info['duration'])
                    break

    def plan_fixed_range(self, city, day_range, duration):
        start_day, end_day = day_range
        if start_day > self.current_day:
            self.plan_gap(start_day - self.current_day)
        self.plan_city(city, duration)
        self.current_day += duration

    def plan_city(self, city, duration):
        self.cities[city]['visited'] = True
        self.itinerary.append({'day_range': f'Day {self.current_day}-{self.current_day + duration - 1}', 'place': city})
        self.current_day += duration

    def plan_gap(self, days):
        self.itinerary.append({'flying': f'Day {self.current_day}-{self.current_day}', 'from': 'None', 'to': 'None'})
        self.current_day += days

    def plan_transition(self, from_city, to_city):
        self.itinerary.append({'flying': f'Day {self.current_day}-{self.current_day}', 'from': from_city, 'to': to_city})

    def print_itinerary(self):
        print(json.dumps(self.itinerary, indent=4))


if __name__ == '__main__':
    planner = TripPlanner()
    planner.plan_trip()
    planner.print_itinerary()