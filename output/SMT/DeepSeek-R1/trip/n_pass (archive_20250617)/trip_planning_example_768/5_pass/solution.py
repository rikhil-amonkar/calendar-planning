from z3 import *

def main():
    City, (Mykonos, Nice, London, Copenhagen, Oslo, Tallinn) = EnumSort('City', ['Mykonos','Nice','London','Copenhagen','Oslo','Tallinn'])
    city_names = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    n_days = 16
    solver = Solver()

    points = [Const(f'point_{i}', City) for i in range(17)]
    solver.add(points[0] == Mykonos)
    solver.add(points[16] == Nice)

    allowed_edges = [
        (Mykonos, London), (London, Mykonos),
        (Mykonos, Nice), (Nice, Mykonos),
        (London, Nice), (Nice, London),
        (London, Copenhagen), (Copenhagen, London),
        (London, Oslo), (Oslo, London),
        (Copenhagen, Tallinn), (Tallinn, Copenhagen),
        (Copenhagen, Nice), (Nice, Copenhagen),
        (Copenhagen, Oslo), (Oslo, Copenhagen),
        (Oslo, Tallinn), (Tallinn, Oslo),
        (Oslo, Nice), (Nice, Oslo)
    ]

    for i in range(16):
        start = points[i]
        end = points[i+1]
        solver.add(Or(start == end, Or([And(start == a, end == b) for (a,b) in allowed_edges])))

    given_days = [4, 3, 2, 3, 5, 4]
    cities = [Mykonos, Nice, London, Copenhagen, Oslo, Tallinn]
    for idx, city in enumerate(cities):
        total = 0
        for i in range(16):
            total += If(Or(points[i] == city, points[i+1] == city), 1, 0)
        solver.add(total == given_days[idx])

    for city in cities:
        for start in range(13):
            solver.add(Not(And(
                Or(points[start] == city, points[start+1] == city),
                Or(points[start+1] == city, points[start+2] == city),
                Or(points[start+2] == city, points[start+3] == city),
                Or(points[start+3] == city, points[start+4] == city)
            ))

    oslo_days = []
    for i in [9, 10, 11, 12, 13]:
        oslo_days.append(Or(points[i] == Oslo, points[i+1] == Oslo))
    solver.add(Or(oslo_days))

    if solver.check() == sat:
        model = solver.model()
        for i in range(16):
            start_val = model.evaluate(points[i], model_completion=True)
            end_val = model.evaluate(points[i+1], model_completion=True)
            start_city = city_names[cities.index(start_val)]
            end_city = city_names[cities.index(end_val)]
            if start_val == end_val:
                print(f"Day {i+1}: stay in {start_city}")
            else:
                print(f"Day {i+1}: fly from {start_city} to {end_city}; therefore in {start_city} and {end_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()