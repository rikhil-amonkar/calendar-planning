import z3
import json
import sys

def main():
    data = json.loads(sys.stdin.read())
    start_city = data['start_city']
    cities = data['cities']
    max_drive = data['max_drive']
    max_time = data['max_time']
    avg_speed = data['avg_speed']
    visit_time = data['visit_time']
    prerequisites = data['prerequisites']
    distance_data = data['distances']

    def get_distance(city1, city2):
        if city1 == city2:
            return 0
        if city1 in distance_data:
            if city2 in distance_data[city1]:
                return distance_data[city1][city2]
        if city2 in distance_data:
            if city1 in distance_data[city2]:
                return distance_data[city2][city1]
        raise ValueError(f"Distance between {city1} and {city2} not found")

    remaining_cities = [city for city in cities if city != start_city]
    n_remaining = len(remaining_cities)

    if n_remaining == 0:
        print(json.dumps([start_city, start_city]))
        return

    s = z3.Solver()
    n = n_remaining

    city_at = [z3.Int(f'city_at_{i}') for i in range(n)]
    
    for i in range(n):
        s.add(city_at[i] >= 0, city_at[i] < n)
    s.add(z3.Distinct(city_at))

    dist_matrix = []
    for i in range(n):
        row = []
        for j in range(n):
            d = get_distance(remaining_cities[i], remaining_cities[j])
            row.append(d)
        dist_matrix.append(row)
    
    dist_start = [get_distance(start_city, city) for city in remaining_cities]
    dist_end = [get_distance(city, start_city) for city in remaining_cities]
    
    matrix_1d = []
    for i in range(n):
        for j in range(n):
            matrix_1d.append(dist_matrix[i][j])
    
    matrix_arr = z3.Array('matrix_arr', z3.IntSort(), z3.IntSort())
    for idx in range(n * n):
        s.add(matrix_arr[idx] == matrix_1d[idx])
    
    start_arr = z3.Array('start_arr', z3.IntSort(), z3.IntSort())
    for i in range(n):
        s.add(start_arr[i] == dist_start[i])
    
    end_arr = z3.Array('end_arr', z3.IntSort(), z3.IntSort())
    for i in range(n):
        s.add(end_arr[i] == dist_end[i])
    
    total_dist = start_arr[city_at[0]]
    for i in range(n - 1):
        index_expr = city_at[i] * n + city_at[i+1]
        total_dist = total_dist + matrix_arr[index_expr]
    total_dist = total_dist + end_arr[city_at[n-1]]
    
    s.add(total_dist <= max_drive)
    
    total_time = total_dist / avg_speed + n * visit_time
    s.add(total_time <= max_time)
    
    pos_of_func = z3.Function('pos_of_func', z3.IntSort(), z3.IntSort())
    for pos_index in range(n):
        s.add(pos_of_func(city_at[pos_index]) == pos_index)
    
    for city, prereq_city in prerequisites.items():
        if city in remaining_cities and prereq_city in remaining_cities:
            city_index = remaining_cities.index(city)
            prereq_index = remaining_cities.index(prereq_city)
            s.add(pos_of_func(prereq_index) < pos_of_func(city_index))
    
    if s.check() == z3.sat:
        m = s.model()
        route_indices = []
        for i in range(n):
            var = city_at[i]
            val = m[var].as_long()
            route_indices.append(val)
        ordered_cities = [remaining_cities[i] for i in route_indices]
        route = [start_city] + ordered_cities + [start_city]
        print(json.dumps(route))
    else:
        print(json.dumps(None))

if __name__ == '__main__':
    main()