#include <stdbool.h>
#include <string.h>
#include <stdlib.h>

#ifndef __CPROVER
void __CPROVER_assume(bool condition);
void __CPROVER_assert(bool condition, const char *message);
#endif

#define __CPROVER_unique_domain(field, field_domain_array)                                  {                                                                                               size_t index;                                                                               __CPROVER_assume(index < (sizeof(field_domain_array) / sizeof(field_domain_array[0])));     __CPROVER_assume(!field_domain_array##_used[index]);                                        field_domain_array##_used[index] = true;                                                    field = field_domain_array[index];                                                      }

size_t __CPROVER_nondet_array_index(size_t length) {
    size_t index;
    __CPROVER_assume(index < length);
    return index;
}

#define __CPROVER_nondet_index(array)                                  __CPROVER_nondet_array_index(sizeof(array) / sizeof(array[0]))

#define __CPROVER_nondet_element(array)        (array)[__CPROVER_nondet_index(array)]

static size_t __CPROVER_index_tmp;

static size_t __CPROVER_index_dispatch(bool comparison) {
    __CPROVER_assume(comparison);
    return __CPROVER_index_tmp;
}

#define __CPROVER_index(array, value)     __CPROVER_index_dispatch(array[__CPROVER_index_tmp = __CPROVER_nondet_index(array)] == value)

struct Entity {
    int house_number;
    const char * favorite_color;
    const char * favorite_vegetable;
    const char * name;
    const char * occupation;
};

static int Entity_house_number[] = {1, 2, 3};
static bool Entity_house_number_used[3];
static const char * Entity_favorite_color[] = {"blue", "teal", "pink"};
static bool Entity_favorite_color_used[3];
static const char * Entity_favorite_vegetable[] = {"tomato", "carrot", "bell pepper"};
static bool Entity_favorite_vegetable_used[3];
static const char * Entity_name[] = {"john", "benjamin", "lisa"};
static bool Entity_name_used[3];
static const char * Entity_occupation[] = {"teacher", "programmer", "musician"};
static bool Entity_occupation_used[3];

static void init_Entity(struct Entity * instance) {
    __CPROVER_unique_domain(instance->house_number, Entity_house_number);
    __CPROVER_unique_domain(instance->favorite_color, Entity_favorite_color);
    __CPROVER_unique_domain(instance->favorite_vegetable, Entity_favorite_vegetable);
    __CPROVER_unique_domain(instance->name, Entity_name);
    __CPROVER_unique_domain(instance->occupation, Entity_occupation);
}

struct PuzzleSolution {
    struct Entity entities[3];
};

static void init_PuzzleSolution(struct PuzzleSolution * instance) {
    for (size_t i = 0; i < sizeof(instance->entities) / sizeof(instance->entities[0]); ++i) {
        init_Entity(&instance->entities[i]);
    }
}

static void validate(struct PuzzleSolution solution) {
    typeof(__CPROVER_nondet_element(solution.entities)) entity_0 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_0.favorite_vegetable == "tomato");
    typeof(__CPROVER_nondet_element(solution.entities)) entity_1 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_1.occupation == "programmer");
    __CPROVER_assume(__CPROVER_abs(entity_0.house_number - entity_1.house_number) == 1);
    ;
    typeof(__CPROVER_nondet_element(solution.entities)) entity_2 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_2.favorite_vegetable == "carrot");
    typeof(__CPROVER_nondet_element(solution.entities)) entity_3 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_3.favorite_vegetable == "bell pepper");
    __CPROVER_assume(entity_2.house_number == entity_3.house_number + 1);
    ;
    typeof(__CPROVER_nondet_element(solution.entities)) entity_4 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_4.favorite_vegetable == "carrot");
    typeof(__CPROVER_nondet_element(solution.entities)) entity_5 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_5.name == "lisa");
    __CPROVER_assume(entity_4.house_number == entity_5.house_number);
    ;
    typeof(__CPROVER_nondet_element(solution.entities)) entity_6 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_6.favorite_color == "pink");
    typeof(__CPROVER_nondet_element(solution.entities)) entity_7 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_7.name == "john");
    __CPROVER_assume(__CPROVER_abs(entity_6.house_number - entity_7.house_number) == 1);
    ;
    typeof(__CPROVER_nondet_element(solution.entities)) entity_8 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_8.favorite_vegetable == "bell pepper");
    typeof(__CPROVER_nondet_element(solution.entities)) entity_9 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_9.favorite_color == "teal");
    __CPROVER_assume(entity_8.house_number == entity_9.house_number - 1);
    ;
    typeof(__CPROVER_nondet_element(solution.entities)) entity_10 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_10.occupation == "musician");
    typeof(__CPROVER_nondet_element(solution.entities)) entity_11 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_11.occupation == "programmer");
    __CPROVER_assume(entity_10.house_number == entity_11.house_number - 1);
    ;
    typeof(__CPROVER_nondet_element(solution.entities)) entity_12 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_12.favorite_color == "pink");
    typeof(__CPROVER_nondet_element(solution.entities)) entity_13 = __CPROVER_nondet_element(solution.entities);
    __CPROVER_assume(entity_13.occupation == "musician");
    __CPROVER_assume(__CPROVER_abs(entity_12.house_number - entity_13.house_number) == 1);
    ;
}

#ifndef __CPROVER
void __CPROVER_output(const char *name, struct PuzzleSolution solution);
#endif

int main(void) {
    struct PuzzleSolution solution;
    init_PuzzleSolution(&solution);
    validate(solution);

    __CPROVER_output("solution", solution);
    __CPROVER_assert(false, "");
}