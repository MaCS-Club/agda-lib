# agda-lib

## Установка

Для сборки данного репозитория использовался не выпущенная версия Agda 2.6.0.

Для пользователей Stack достаточно добавить в файл `~/.stack/global-project/stack.yaml`:

```yaml
extra-deps:
   - git: https://github.com/agda/agda.git
     commit: d26b34bfc23f745d96c3cd1c5ee0e76caf9531d4 # коммит который использовался при разработке данного репозитория
```
