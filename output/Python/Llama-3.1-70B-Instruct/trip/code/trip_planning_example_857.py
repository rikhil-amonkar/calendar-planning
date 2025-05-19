import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Porto': {'duration': 2, 'fixed_range': None, 'visited': False},
            'Geneva': {'duration': 3, 'fixed_range': None, 'visited': False},
            'Mykonos': {'duration': 3, 'fixed_range': (10, 12), 'visited': False},
            'Manchester': {'duration': 4, 'fixed_range': (15, 18), 'visited': False},
            'Hamburg': {'duration': 5, 'fixed_range': None, 'visited': False},
            'Naples': {'duration': 5, 'fixed_range': None, 'visited': False},
            'Frankfurt': {'duration': 2, 'fixed_range': (5, 6), 'visited': False},
        }
        self.direct_flights = [
            ('Hamburg', 'Frankfurt'), ('Naples', 'Mykonos'), ('Hamburg', 'Porto'), 
            ('Hamburg', 'Geneva'), ('Mykonos', 'Geneva'), ('Frankfurt', 'Geneva'), 
            ('Frankfurt', 'Porto'), ('Geneva', 'Porto'), ('Geneva', 'Manchester'), 
            ('Naples', 'Manchester'), ('Frankfurt', 'Naples'), ('Frankfurt', 'Manchester'), 
            ('Naples', 'Geneva'), ('Porto', 'Manchester'), ('Hamburg', 'Manchester')
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