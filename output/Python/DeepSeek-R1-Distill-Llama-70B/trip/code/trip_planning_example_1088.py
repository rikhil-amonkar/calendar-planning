import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Reykjavik': 2,
            'Stockholm': 3,
            'Oslo': 5,
            'Stuttgart': 5,
            'Split': 3,
            'Geneva': 2,
            'Porto': 3,
            'Tallinn': 5
        }
        self.flights = {
            'Reykjavik': ['Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'],
            'Stockholm': ['Stuttgart', 'Split', 'Geneva', 'Oslo'],
            'Oslo': ['Split', 'Geneva', 'Porto', 'Tallinn'],
            'Stuttgart': ['Porto'],
            'Split': ['Stuttgart'],
            'Geneva': ['Porto', 'Split'],
            'Porto': [],
            'Tallinn': ['Oslo']
        }
        self.itinerary = []
        self.current_day = 1
        self.current_city = None

    def plan_trip(self):
        self.current_city = 'Reykjavik'
        self.stay('Reykjavik', 2)
        self.visit_next_city()
        return self.itinerary

    def visit_next_city(self):
        while self.current_day <= 21:
            next_cities = self.flights[self.current_city]
            for city in next_cities:
                if city in self.cities and self.cities[city] > 0:
                    self.fly_to(city)
                    self.stay(city, self.cities[city])
                    self.visit_next_city()
                    break
            else:
                break

    def stay(self, city, days):
        self.itinerary.append({'day_range': f'Day {self.current_day}-{self.current_day + days - 1}', 'place': city})
        self.current_day += days
        self.cities[city] = 0

    def fly_to(self, city):
        self.itinerary.append({'flying': f'Day {self.current_day - 1}-{self.current_day - 1}', 'from': self.current_city, 'to': city})
        self.current_city = city

planner = TripPlanner()
itinerary = planner.plan_trip()

for i in range(len(itinerary)):
    if 'flying' in itinerary[i]:
        itinerary[i]['flying'] = f"Day {itinerary[i]['flying'].split('-')[0]}-{itinerary[i]['flying'].split('-')[1]}"

print(json.dumps(itinerary, indent=2))