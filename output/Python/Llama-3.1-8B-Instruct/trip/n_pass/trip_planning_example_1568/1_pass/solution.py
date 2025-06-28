import json
from collections import defaultdict

class TripPlanner:
    def __init__(self, cities, days, constraints):
        self.cities = cities
        self.days = days
        self.constraints = constraints
        self.graph = defaultdict(list)
        self.build_graph()

    def build_graph(self):
        for city1, city2 in self.constraints['flights']:
            self.graph[city1].append(city2)
            self.graph[city2].append(city1)

    def find_itinerary(self):
        self.itinerary = {}
        self.place = None
        self.day_range = None
        self.days_in_place = 0
        self.visit_place(self.cities[0], 1)
        return self.itinerary

    def visit_place(self, place, day):
        if self.place == place:
            self.days_in_place += 1
        else:
            self.days_in_place = 1
            self.place = place
            self.day_range = f"Day {day}-{day + self.days_in_place - 1}"
        if self.days_in_place <= self.days:
            self.itinerary[self.day_range] = place
            for neighbor in self.graph[place]:
                if neighbor not in self.constraints['stays']:
                    self.visit_place(neighbor, day + self.days_in_place)
        else:
            self.days_in_place = 0
            self.place = None

def main():
    cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
    days = 20
    constraints = {
        'flights': [
            ('Riga', 'Stockholm'),
            ('Stockholm', 'Brussels'),
            ('Istanbul', 'Munich'),
            ('Istanbul', 'Riga'),
            ('Prague', 'Split'),
            ('Vienna', 'Brussels'),
            ('Vienna', 'Riga'),
            ('Split', 'Stockholm'),
            ('Munich', 'Amsterdam'),
            ('Split', 'Amsterdam'),
            ('Amsterdam', 'Stockholm'),
            ('Amsterdam', 'Riga'),
            ('Vienna', 'Stockholm'),
            ('Vienna', 'Istanbul'),
            ('Vienna', 'Seville'),
            ('Istanbul', 'Amsterdam'),
            ('Munich', 'Brussels'),
            ('Prague', 'Munich'),
            ('Riga', 'Munich'),
            ('Prague', 'Amsterdam'),
            ('Prague', 'Brussels'),
            ('Prague', 'Istanbul'),
            ('Istanbul', 'Stockholm'),
            ('Vienna', 'Prague'),
            ('Munich', 'Split'),
            ('Vienna', 'Amsterdam'),
            ('Prague', 'Stockholm'),
            ('Brussels', 'Seville'),
            ('Munich', 'Stockholm'),
            ('Istanbul', 'Brussels'),
            ('Amsterdam', 'Seville'),
            ('Vienna', 'Split'),
            ('Munich', 'Seville'),
            ('Riga', 'Brussels'),
            ('Prague', 'Riga'),
            ('Vienna', 'Munich')
        ],
       'stays': {
            'Prague': (1, 5),
            'Brussels': (1, 2),
            'Riga': (1, 2),
            'Munich': (1, 2),
            'Seville': (1, 3),
            'Stockholm': (1, 2),
            'Istanbul': (1, 2),
            'Amsterdam': (1, 3),
            'Vienna': (1, 5),
            'Split': (1, 3)
        }
    }
    trip_planner = TripPlanner(cities, days, constraints)
    itinerary = trip_planner.find_itinerary()
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()