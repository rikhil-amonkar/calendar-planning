for city, duration in cities.items():
      for day in range(1, 16 - duration + 2):
          solver.add(Or([And([itinerary_vars[day-1 + d][cities_list.index(city)] for d in range(duration)]) for day in range(1, 16 - duration + 2)]))