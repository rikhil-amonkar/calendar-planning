if s.check() == sat:
    model = s.model()
    rows = []
    for i in range(houses):
        house_num = str(i + 1)
        name_val = model.evaluate(names[i]).decl().name()
        music_val = model.evaluate(musics[i]).decl().name()
        child_val = model.evaluate(childrens[i]).decl().name()
        book_val = model.evaluate(books[i]).decl().name()
        rows.append([house_num, name_val, music_val, child_val, book_val])
    solution = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))